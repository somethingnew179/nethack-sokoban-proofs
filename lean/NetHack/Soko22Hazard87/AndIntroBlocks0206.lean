import NetHack.Soko22Hazard87.AndIntroBlocks0205
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro51500 (p : Pattern) (ha : d17386 p = 1) (hb : d122304 p = 1) : d15780 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13816 q = 1) : d13816 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17381 q = 1) (hb : d122304 q = 1) : d15770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d122304, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17381, d122304, d15770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15779 q = 1) (hb : d122304 q = 1) : d15779 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17386 q = 1) (hb : d122304 q = 1) : d15780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17386, d15780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro51501 (p : Pattern) (ha : d17405 p = 1) (hb : d122304 p = 1) : d15801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d122304 q = 1) : d15772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51498 q ha hb
    | true =>
      simp only [d17383, d15772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d122304 q = 1) : d15773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d122304 q = 1) : d15774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d122304 q = 1) : d15781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
    | true =>
      simp only [d17387, d15781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51500 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d122304 q = 1) : d15782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d15782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d122304 q = 1) : d15783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d15783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d122304 q = 1) : d15784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d122304 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d122304 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d122304 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15795 q = 1) (hb : d122304 q = 1) : d15795 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17400 q = 1) (hb : d122304 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17401 q = 1) (hb : d122304 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17402 q = 1) (hb : d122304 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17403 q = 1) (hb : d122304 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17404 q = 1) (hb : d122304 q = 1) : d15800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d17405 q = 1) (hb : d122304 q = 1) : d15801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17405, d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro51502 (p : Pattern) (ha : d17410 p = 1) (hb : d122304 p = 1) : d15806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d122304 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d122304 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d122304 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d122304 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d122304 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d122304 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d122304 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d122304 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17408 q = 1) (hb : d122304 q = 1) : d15804 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17408, d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d17409 q = 1) (hb : d122304 q = 1) : d15805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17409, d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17410 q = 1) (hb : d122304 q = 1) : d15806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17410, d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro51503 (p : Pattern) (ha : d17416 p = 1) (hb : d122304 p = 1) : d15812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17406 q = 1) (hb : d122304 q = 1) : d15802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17406, d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51501 q ha hb
    | true =>
      simp only [d17406, d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17407 q = 1) (hb : d122304 q = 1) : d15803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17407, d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17407, d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17411 q = 1) (hb : d122304 q = 1) : d15807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51502 q ha hb
    | true =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17412 q = 1) (hb : d122304 q = 1) : d15808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17413 q = 1) (hb : d122304 q = 1) : d15809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17413, d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17413, d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17414 q = 1) (hb : d122304 q = 1) : d15810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17414, d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17414, d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17415 q = 1) (hb : d122304 q = 1) : d15811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17415, d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17415, d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17416 q = 1) (hb : d122304 q = 1) : d15812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17416, d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17416, d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51504 (p : Pattern) (ha : d17428 p = 1) (hb : d122304 p = 1) : d15825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17411 q = 1) (hb : d122304 q = 1) : d15807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51502 q ha hb
    | true =>
      simp only [d17411, d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17412 q = 1) (hb : d122304 q = 1) : d15808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17412, d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d122304 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51475 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d122304 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17425 q = 1) (hb : d122304 q = 1) : d15822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17425, d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17425, d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17426 q = 1) (hb : d122304 q = 1) : d15823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17426, d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17426, d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17427 q = 1) (hb : d122304 q = 1) : d15824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17427, d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17427, d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17428 q = 1) (hb : d122304 q = 1) : d15825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17428, d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17428, d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51505 (p : Pattern) (ha : d17477 p = 1) (hb : d122304 p = 1) : d15882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d122304 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d122304 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d122304 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d122304 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d122304 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d122304 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d122304 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d122304 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d122304 q = 1) : d13843 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17472 q = 1) (hb : d122304 q = 1) : d15877 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17472, d15877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17473 q = 1) (hb : d122304 q = 1) : d15878 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d15878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17474 q = 1) (hb : d122304 q = 1) : d15879 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d15879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17475 q = 1) (hb : d122304 q = 1) : d15880 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17475, d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d17476 q = 1) (hb : d122304 q = 1) : d15881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17476, d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17477 q = 1) (hb : d122304 q = 1) : d15882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17477, d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17477, d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro51506 (p : Pattern) (ha : d17483 p = 1) (hb : d122304 p = 1) : d15888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17478 q = 1) (hb : d122304 q = 1) : d15883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17478, d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51505 q ha hb
    | true =>
      simp only [d17478, d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17479 q = 1) (hb : d122304 q = 1) : d15884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17479, d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17479, d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17480 q = 1) (hb : d122304 q = 1) : d15885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17480, d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17480, d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17481 q = 1) (hb : d122304 q = 1) : d15886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17481, d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17481, d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17482 q = 1) (hb : d122304 q = 1) : d15887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17482, d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17482, d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17483 q = 1) (hb : d122304 q = 1) : d15888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17483, d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17483, d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51507 (p : Pattern) (ha : d122304 p = 1) (hb : d128422 p = 1) : d125682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17429 q = 1) (hb : d122304 q = 1) : d15826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17429, d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51503 q ha hb
    | true =>
      simp only [d17429, d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51504 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128418 q = 1) : d125678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128418, d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d17484 q = 1) (hb : d122304 q = 1) : d15889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17484, d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51506 q ha hb
    | true =>
      simp only [d17484, d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17485 q = 1) (hb : d122304 q = 1) : d15890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17485, d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17485, d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128419 q = 1) : d125679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128419, d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128420 q = 1) : d125680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128420, d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d128421 q = 1) : d125681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128421, d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d128422 q = 1) : d125682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128422, d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51508 (p : Pattern) (ha : d122304 p = 1) (hb : d128428 p = 1) : d125688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17195 q = 1) (hb : d122304 q = 1) : d15590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17195, d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17195, d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51465 q ha hb
  have h2 (q : Pattern) (ha : d17196 q = 1) (hb : d122304 q = 1) : d15591 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17196, d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17196, d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17205 q = 1) (hb : d122304 q = 1) : d15600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51465 q ha hb
    | true =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51468 q ha hb
  have h4 (q : Pattern) (ha : d17206 q = 1) (hb : d122304 q = 1) : d15601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17207 q = 1) (hb : d122304 q = 1) : d15602 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17207, d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17207, d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128406 q = 1) : d125666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128406, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51488 q ha hb
    | true =>
      simp only [d128406, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51496 q ha hb
  have h7 (q : Pattern) (ha : d17355 q = 1) (hb : d122304 q = 1) : d15753 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17355, d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51471 q ha hb
    | true =>
      simp only [d17355, d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51472 q ha hb
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d128407 q = 1) : d125667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128407, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128407, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d128408 q = 1) : d125668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128408, d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d128409 q = 1) : d125669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128409, d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d128413 q = 1) : d125673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128413, d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51497 q ha hb
  have h12 (q : Pattern) (ha : d17364 q = 1) (hb : d122304 q = 1) : d15762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17364, d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17364, d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51473 q ha hb
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d128414 q = 1) : d125674 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128414, d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d128415 q = 1) : d125675 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128415, d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d128416 q = 1) : d125676 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128416, d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122304 q = 1) (hb : d128417 q = 1) : d125677 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128417, d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122304 q = 1) (hb : d128423 q = 1) : d125683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128423, d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51507 q ha hb
  have h18 (q : Pattern) (ha : d17501 q = 1) (hb : d122304 q = 1) : d15906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17501, d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17501, d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51477 q ha hb
  have h19 (q : Pattern) (ha : d122304 q = 1) (hb : d128424 q = 1) : d125684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128424, d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122304 q = 1) (hb : d128425 q = 1) : d125685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128425, d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122304 q = 1) (hb : d128426 q = 1) : d125686 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128426, d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122304 q = 1) (hb : d128427 q = 1) : d125687 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128427, d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122304 q = 1) (hb : d128428 q = 1) : d125688 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128428, d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51509 (p : Pattern) (ha : d122304 p = 1) (hb : d128434 p = 1) : d125694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d128429 q = 1) : d125689 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128429, d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51508 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128430 q = 1) : d125690 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128430, d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d128431 q = 1) : d125691 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128431, d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d128432 q = 1) : d125692 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128432, d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128433 q = 1) : d125693 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128433, d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128434 q = 1) : d125694 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128434, d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51510 (p : Pattern) (ha : d122304 p = 1) (hb : d128440 p = 1) : d125700 p = 1 := by
  have h0 (q : Pattern) (ha : d122304 q = 1) (hb : d128269 q = 1) : d125529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51268 q ha hb
    | true =>
      simp only [d128269, d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51310 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128309 q = 1) : d125569 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128309, d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51356 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d128310 q = 1) : d125570 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d128350 q = 1) : d125610 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128350, d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51407 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128351 q = 1) : d125611 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128351, d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128352 q = 1) : d125612 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d128392 q = 1) : d125652 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128392, d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51458 q ha hb
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d128393 q = 1) : d125653 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128393, d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d128394 q = 1) : d125654 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128394, d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d128395 q = 1) : d125655 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d128435 q = 1) : d125695 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128435, d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51509 q ha hb
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d128436 q = 1) : d125696 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128436, d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d128437 q = 1) : d125697 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128437, d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d128438 q = 1) : d125698 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128438, d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d128439 q = 1) : d125699 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122304 q = 1) (hb : d128440 q = 1) : d125700 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro51511 (p : Pattern) (ha : d122304 p = 1) (hb : d128446 p = 1) : d125706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d128441 q = 1) : d125701 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51510 q ha hb
    | true =>
      simp only [d128441, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128442 q = 1) : d125702 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d128443 q = 1) : d125703 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d128444 q = 1) : d125704 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128445 q = 1) : d125705 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128446 q = 1) : d125706 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51512 (p : Pattern) (ha : d122304 p = 1) (hb : d128452 p = 1) : d125712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d128447 q = 1) : d125707 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51511 q ha hb
    | true =>
      simp only [d128447, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128448 q = 1) : d125708 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d128449 q = 1) : d125709 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d128450 q = 1) : d125710 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128451 q = 1) : d125711 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d128452 q = 1) : d125712 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51513 (p : Pattern) (ha : d128458 p = 1) (hb : d163444 p = 1) : d125718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d128453 q = 1) : d125713 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51512 q ha hb
    | true =>
      simp only [d128453, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d128454 q = 1) : d125714 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d128455 q = 1) : d125715 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d128456 q = 1) : d125716 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d128457 q = 1) : d125717 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d128458 q = 1) (hb : d163444 q = 1) : d125718 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d163444, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128458, d163444, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51514 (p : Pattern) (ha : d128464 p = 1) (hb : d163444 p = 1) : d125724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d163444 q = 1) : d125719 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51513 q ha hb
    | true =>
      simp only [d128459, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d163444 q = 1) : d125720 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d163444 q = 1) : d125721 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d163444 q = 1) : d125722 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d163444 q = 1) : d125723 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d163444 q = 1) : d125724 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51515 (p : Pattern) (ha : d128470 p = 1) (hb : d163444 p = 1) : d125730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d163444 q = 1) : d125725 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51514 q ha hb
    | true =>
      simp only [d128465, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d163444 q = 1) : d125726 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d163444 q = 1) : d125727 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d163444 q = 1) : d125728 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d163444 q = 1) : d125729 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d163444 q = 1) : d125730 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51516 (p : Pattern) (ha : d128476 p = 1) (hb : d163444 p = 1) : d125736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d163444 q = 1) : d125731 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51515 q ha hb
    | true =>
      simp only [d128471, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d163444 q = 1) : d125732 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d163444 q = 1) : d125733 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d163444 q = 1) : d125734 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d163444 q = 1) : d125735 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d163444 q = 1) : d125736 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51517 (p : Pattern) (ha : d128482 p = 1) (hb : d163444 p = 1) : d125742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d163444 q = 1) : d125737 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51516 q ha hb
    | true =>
      simp only [d128477, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d163444 q = 1) : d125738 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d163444 q = 1) : d125739 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d163444 q = 1) : d125740 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d163444 q = 1) : d125741 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d163444 q = 1) : d125742 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51518 (p : Pattern) (ha : d53655 p = 1) (hb : d122304 p = 1) : d163447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122304 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d122304 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51236 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d122304 q = 1) : d14057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d122304 q = 1) : d14058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d122304 q = 1) : d14059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d122304 q = 1) : d14060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d122304 q = 1) : d163447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51519 (p : Pattern) (ha : d53665 p = 1) (hb : d122304 p = 1) : d163457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122304 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d122304 q = 1) : d14033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51240 q ha hb
    | true =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d122304 q = 1) : d163453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d122304 q = 1) : d163454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d122304 q = 1) : d163455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d122304 q = 1) : d163456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d122304 q = 1) : d163457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51520 (p : Pattern) (ha : d53671 p = 1) (hb : d122304 p = 1) : d163463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d122304 q = 1) : d14062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51246 q ha hb
    | true =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51247 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d122304 q = 1) : d14063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d122304 q = 1) : d163445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d122304 q = 1) : d163446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d122304 q = 1) : d163448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51518 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d122304 q = 1) : d163449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d122304 q = 1) : d163450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d122304 q = 1) : d163451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d122304 q = 1) : d163452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d122304 q = 1) : d163458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51519 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d122304 q = 1) : d163459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d122304 q = 1) : d163460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d122304 q = 1) : d163461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d122304 q = 1) : d163462 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d122304 q = 1) : d163463 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51521 (p : Pattern) (ha : d53677 p = 1) (hb : d122304 p = 1) : d163469 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d122304 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d122304 q = 1) : d163464 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51520 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d122304 q = 1) : d163465 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d122304 q = 1) : d163466 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d122304 q = 1) : d163467 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d122304 q = 1) : d163468 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d122304 q = 1) : d163469 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51522 (p : Pattern) (ha : d122304 p = 1) (hb : d171078 p = 1) : d163472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d122304 q = 1) : d14235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51280 q ha hb
    | true =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51271 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d122304 q = 1) : d14236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d122304 q = 1) : d14237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d122304 q = 1) : d14238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d122304 q = 1) : d14239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171078 q = 1) : d163472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171078, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro51523 (p : Pattern) (ha : d122304 p = 1) (hb : d171089 p = 1) : d163483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171084 q = 1) : d163478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51306 q hb ha
    | true =>
      simp only [d171084, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51275 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171085 q = 1) : d163479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171085, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171086 q = 1) : d163480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171087 q = 1) : d163481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171087, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171088 q = 1) : d163482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171088, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171089 q = 1) : d163483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171089, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51524 (p : Pattern) (ha : d122304 p = 1) (hb : d171095 p = 1) : d163489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d122304 q = 1) : d14241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51279 q ha hb
    | true =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51281 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d122304 q = 1) : d14242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171076 q = 1) : d163470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171076, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171077 q = 1) : d163471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171077, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171079 q = 1) : d163473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171079, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51522 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171080 q = 1) : d163474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171081 q = 1) : d163475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171082 q = 1) : d163476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171083 q = 1) : d163477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171090 q = 1) : d163484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171090, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51523 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171091 q = 1) : d163485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171092 q = 1) : d163486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171093 q = 1) : d163487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171094 q = 1) : d163488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171095 q = 1) : d163489 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51525 (p : Pattern) (ha : d122304 p = 1) (hb : d171101 p = 1) : d163495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171096 q = 1) : d163490 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171096, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51524 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171097 q = 1) : d163491 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171097, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171098 q = 1) : d163492 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171098, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171099 q = 1) : d163493 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171099, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171100 q = 1) : d163494 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171100, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171101 q = 1) : d163495 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171101, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51526 (p : Pattern) (ha : d122304 p = 1) (hb : d171105 p = 1) : d163499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d122304 q = 1) : d14502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51325 q ha hb
    | true =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51314 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d122304 q = 1) : d14503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d122304 q = 1) : d14504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d122304 q = 1) : d14505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d122304 q = 1) : d14506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171105 q = 1) : d163499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171105, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro51527 (p : Pattern) (ha : d122304 p = 1) (hb : d171116 p = 1) : d163510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171111 q = 1) : d163505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51352 q hb ha
    | true =>
      simp only [d171111, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51319 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171112 q = 1) : d163506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171112, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171113 q = 1) : d163507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171114 q = 1) : d163508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171114, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171115 q = 1) : d163509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171115, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171116 q = 1) : d163510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171116, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51528 (p : Pattern) (ha : d122304 p = 1) (hb : d171122 p = 1) : d163516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d122304 q = 1) : d14508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51324 q ha hb
    | true =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51326 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d122304 q = 1) : d14509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171103 q = 1) : d163497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171103, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171104 q = 1) : d163498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171104, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171106 q = 1) : d163500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171106, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51526 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171107 q = 1) : d163501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171108 q = 1) : d163502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171109 q = 1) : d163503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171110 q = 1) : d163504 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171117 q = 1) : d163511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171117, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51527 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171118 q = 1) : d163512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171119 q = 1) : d163513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171120 q = 1) : d163514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171121 q = 1) : d163515 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171122 q = 1) : d163516 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51529 (p : Pattern) (ha : d122304 p = 1) (hb : d171128 p = 1) : d163522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171123 q = 1) : d163517 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171123, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51528 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171124 q = 1) : d163518 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171124, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171125 q = 1) : d163519 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171125, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171126 q = 1) : d163520 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171126, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171127 q = 1) : d163521 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171127, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171128 q = 1) : d163522 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171128, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51530 (p : Pattern) (ha : d122304 p = 1) (hb : d171133 p = 1) : d163527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d122304 q = 1) : d14809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51364 q ha hb
    | true =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51365 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d122304 q = 1) : d14810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d122304 q = 1) : d14811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d122304 q = 1) : d14812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d122304 q = 1) : d14813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171133 q = 1) : d163527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171133, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro51531 (p : Pattern) (ha : d122304 p = 1) (hb : d171140 p = 1) : d163534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d122304 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51397 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51372 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d122304 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d122304 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d122304 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d122304 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51372 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d122304 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d122304 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d122304 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15042 q = 1) (hb : d122304 q = 1) : d15042 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16693 q = 1) (hb : d122304 q = 1) : d15043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51372 q ha hb
    | true =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16694 q = 1) (hb : d122304 q = 1) : d15044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16695 q = 1) (hb : d122304 q = 1) : d15045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16696 q = 1) (hb : d122304 q = 1) : d15046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171139 q = 1) : d163533 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171139, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171140 q = 1) : d163534 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171140, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro51532 (p : Pattern) (ha : d122304 p = 1) (hb : d171146 p = 1) : d163540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171141 q = 1) : d163535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51531 q ha hb
    | true =>
      simp only [d171141, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171142 q = 1) : d163536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171142, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d122304 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51373 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d122304 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171143 q = 1) : d163537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171144 q = 1) : d163538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171145 q = 1) : d163539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171146 q = 1) : d163540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51533 (p : Pattern) (ha : d122304 p = 1) (hb : d171152 p = 1) : d163546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171147 q = 1) : d163541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51532 q ha hb
    | true =>
      simp only [d171147, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51374 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171148 q = 1) : d163542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171148, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171149 q = 1) : d163543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171150 q = 1) : d163544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171150, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171151 q = 1) : d163545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171151, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171152 q = 1) : d163546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171152, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51534 (p : Pattern) (ha : d122304 p = 1) (hb : d171158 p = 1) : d163552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d122304 q = 1) : d14815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51363 q ha hb
    | true =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51366 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d122304 q = 1) : d14816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171131 q = 1) : d163525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171131, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171132 q = 1) : d163526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171132, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171134 q = 1) : d163528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171134, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51530 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171135 q = 1) : d163529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171136 q = 1) : d163530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171137 q = 1) : d163531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171138 q = 1) : d163532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171153 q = 1) : d163547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171153, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51533 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171154 q = 1) : d163548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171155 q = 1) : d163549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171156 q = 1) : d163550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171157 q = 1) : d163551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171158 q = 1) : d163552 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51535 (p : Pattern) (ha : d122304 p = 1) (hb : d171164 p = 1) : d163558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171159 q = 1) : d163553 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171159, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51534 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171160 q = 1) : d163554 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171160, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171161 q = 1) : d163555 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171161, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171162 q = 1) : d163556 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171162, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171163 q = 1) : d163557 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171163, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171164 q = 1) : d163558 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171164, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51536 (p : Pattern) (ha : d122304 p = 1) (hb : d171170 p = 1) : d163564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d122304 q = 1) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51415 q ha hb
    | true =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51416 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d122304 q = 1) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d122304 q = 1) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d122304 q = 1) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d122304 q = 1) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171170 q = 1) : d163564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171170, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro51537 (p : Pattern) (ha : d122304 p = 1) (hb : d171177 p = 1) : d163571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d122304 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51448 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51423 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d122304 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d122304 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d122304 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d122304 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51423 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d122304 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d122304 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d122304 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15435 q = 1) (hb : d122304 q = 1) : d15435 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17053 q = 1) (hb : d122304 q = 1) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51423 q ha hb
    | true =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17054 q = 1) (hb : d122304 q = 1) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17055 q = 1) (hb : d122304 q = 1) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17056 q = 1) (hb : d122304 q = 1) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171176 q = 1) : d163570 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171176, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171177 q = 1) : d163571 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171177, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro51538 (p : Pattern) (ha : d122304 p = 1) (hb : d171183 p = 1) : d163577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171178 q = 1) : d163572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51537 q ha hb
    | true =>
      simp only [d171178, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171179 q = 1) : d163573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171179, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d122304 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51424 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d122304 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171180 q = 1) : d163574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171181 q = 1) : d163575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171182 q = 1) : d163576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171183 q = 1) : d163577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51539 (p : Pattern) (ha : d122304 p = 1) (hb : d171189 p = 1) : d163583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171184 q = 1) : d163578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51538 q ha hb
    | true =>
      simp only [d171184, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51425 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171185 q = 1) : d163579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171185, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171186 q = 1) : d163580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171187 q = 1) : d163581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171187, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171188 q = 1) : d163582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171188, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171189 q = 1) : d163583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171189, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51540 (p : Pattern) (ha : d122304 p = 1) (hb : d171195 p = 1) : d163589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d122304 q = 1) : d15208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51414 q ha hb
    | true =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51417 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d122304 q = 1) : d15209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171168 q = 1) : d163562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171168, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171169 q = 1) : d163563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171169, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171171 q = 1) : d163565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171171, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51536 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171172 q = 1) : d163566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171173 q = 1) : d163567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171174 q = 1) : d163568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171175 q = 1) : d163569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171190 q = 1) : d163584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171190, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51539 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171191 q = 1) : d163585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171192 q = 1) : d163586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171193 q = 1) : d163587 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171194 q = 1) : d163588 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171195 q = 1) : d163589 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51541 (p : Pattern) (ha : d122304 p = 1) (hb : d171201 p = 1) : d163595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171196 q = 1) : d163590 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171196, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51540 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171197 q = 1) : d163591 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171197, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171198 q = 1) : d163592 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171198, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171199 q = 1) : d163593 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171199, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171200 q = 1) : d163594 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171200, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171201 q = 1) : d163595 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171201, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51542 (p : Pattern) (ha : d122304 p = 1) (hb : d171208 p = 1) : d163602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d122304 q = 1) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51466 q ha hb
    | true =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51467 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d122304 q = 1) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d122304 q = 1) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d122304 q = 1) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d122304 q = 1) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171208 q = 1) : d163602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171208, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro51543 (p : Pattern) (ha : d122304 p = 1) (hb : d171215 p = 1) : d163609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d122304 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51499 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d122304 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d122304 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d122304 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d122304 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d122304 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d122304 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d122304 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15813 q = 1) (hb : d122304 q = 1) : d15813 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17417 q = 1) (hb : d122304 q = 1) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51474 q ha hb
    | true =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17418 q = 1) (hb : d122304 q = 1) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17419 q = 1) (hb : d122304 q = 1) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17420 q = 1) (hb : d122304 q = 1) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171214 q = 1) : d163608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171214, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171215 q = 1) : d163609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171215, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro51544 (p : Pattern) (ha : d122304 p = 1) (hb : d171221 p = 1) : d163615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171216 q = 1) : d163610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51543 q ha hb
    | true =>
      simp only [d171216, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171217 q = 1) : d163611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171217, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d122304 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51475 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d122304 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171218 q = 1) : d163612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171219 q = 1) : d163613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171220 q = 1) : d163614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171221 q = 1) : d163615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro51545 (p : Pattern) (ha : d122304 p = 1) (hb : d171227 p = 1) : d163621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171222 q = 1) : d163616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51544 q ha hb
    | true =>
      simp only [d171222, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51476 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171223 q = 1) : d163617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171223, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171224 q = 1) : d163618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171225 q = 1) : d163619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171225, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171226 q = 1) : d163620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171226, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171227 q = 1) : d163621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171227, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51546 (p : Pattern) (ha : d122304 p = 1) (hb : d171233 p = 1) : d163627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d122304 q = 1) : d15600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51465 q ha hb
    | true =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51468 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d122304 q = 1) : d15601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171206 q = 1) : d163600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171206, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171207 q = 1) : d163601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171207, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171209 q = 1) : d163603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171209, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51542 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171210 q = 1) : d163604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171211 q = 1) : d163605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171212 q = 1) : d163606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171213 q = 1) : d163607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171228 q = 1) : d163622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171228, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51545 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171229 q = 1) : d163623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171230 q = 1) : d163624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171231 q = 1) : d163625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171232 q = 1) : d163626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171233 q = 1) : d163627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51547 (p : Pattern) (ha : d122304 p = 1) (hb : d171239 p = 1) : d163633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171234 q = 1) : d163628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171234, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51546 q ha hb
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171235 q = 1) : d163629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171235, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171236 q = 1) : d163630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171236, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171237 q = 1) : d163631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171237, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171238 q = 1) : d163632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171238, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171239 q = 1) : d163633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171239, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51548 (p : Pattern) (ha : d122304 p = 1) (hb : d171245 p = 1) : d163639 p = 1 := by
  have h0 (q : Pattern) (ha : d122304 q = 1) (hb : d171102 q = 1) : d163496 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51521 q hb ha
    | true =>
      simp only [d171102, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51525 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171129 q = 1) : d163523 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171129, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51529 q ha hb
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171130 q = 1) : d163524 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171165 q = 1) : d163559 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171165, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51535 q ha hb
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171166 q = 1) : d163560 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171166, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171167 q = 1) : d163561 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122304 q = 1) (hb : d171202 q = 1) : d163596 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171202, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51541 q ha hb
  have h8 (q : Pattern) (ha : d122304 q = 1) (hb : d171203 q = 1) : d163597 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171203, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122304 q = 1) (hb : d171204 q = 1) : d163598 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171204, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122304 q = 1) (hb : d171205 q = 1) : d163599 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122304 q = 1) (hb : d171240 q = 1) : d163634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171240, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51547 q ha hb
  have h12 (q : Pattern) (ha : d122304 q = 1) (hb : d171241 q = 1) : d163635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171241, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122304 q = 1) (hb : d171242 q = 1) : d163636 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171242, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122304 q = 1) (hb : d171243 q = 1) : d163637 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171243, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122304 q = 1) (hb : d171244 q = 1) : d163638 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122304 q = 1) (hb : d171245 q = 1) : d163639 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro51549 (p : Pattern) (ha : d122304 p = 1) (hb : d171251 p = 1) : d163645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171246 q = 1) : d163640 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51548 q ha hb
    | true =>
      simp only [d171246, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171247 q = 1) : d163641 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171248 q = 1) : d163642 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171249 q = 1) : d163643 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171250 q = 1) : d163644 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171251 q = 1) : d163645 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51550 (p : Pattern) (ha : d122304 p = 1) (hb : d171257 p = 1) : d163651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171252 q = 1) : d163646 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51549 q ha hb
    | true =>
      simp only [d171252, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171253 q = 1) : d163647 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171254 q = 1) : d163648 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171255 q = 1) : d163649 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171256 q = 1) : d163650 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122304 q = 1) (hb : d171257 q = 1) : d163651 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51551 (p : Pattern) (ha : d163444 p = 1) (hb : d171263 p = 1) : d163657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122304 q = 1) (hb : d171258 q = 1) : d163652 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51550 q ha hb
    | true =>
      simp only [d171258, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122304 q = 1) (hb : d171259 q = 1) : d163653 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122304 q = 1) (hb : d171260 q = 1) : d163654 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122304 q = 1) (hb : d171261 q = 1) : d163655 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122304 q = 1) (hb : d171262 q = 1) : d163656 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d163444 q = 1) (hb : d171263 q = 1) : d163657 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163444, d171263, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163444, d171263, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51552 (p : Pattern) (ha : d163444 p = 1) (hb : d171269 p = 1) : d163663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163444 q = 1) (hb : d171264 q = 1) : d163658 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51551 q ha hb
    | true =>
      simp only [d171264, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163444 q = 1) (hb : d171265 q = 1) : d163659 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163444 q = 1) (hb : d171266 q = 1) : d163660 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163444 q = 1) (hb : d171267 q = 1) : d163661 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163444 q = 1) (hb : d171268 q = 1) : d163662 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163444 q = 1) (hb : d171269 q = 1) : d163663 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51553 (p : Pattern) (ha : d163444 p = 1) (hb : d171275 p = 1) : d163669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163444 q = 1) (hb : d171270 q = 1) : d163664 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51552 q ha hb
    | true =>
      simp only [d171270, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163444 q = 1) (hb : d171271 q = 1) : d163665 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163444 q = 1) (hb : d171272 q = 1) : d163666 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163444 q = 1) (hb : d171273 q = 1) : d163667 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163444 q = 1) (hb : d171274 q = 1) : d163668 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163444 q = 1) (hb : d171275 q = 1) : d163669 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51554 (p : Pattern) (ha : d163444 p = 1) (hb : d171281 p = 1) : d163675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163444 q = 1) (hb : d171276 q = 1) : d163670 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51553 q ha hb
    | true =>
      simp only [d171276, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163444 q = 1) (hb : d171277 q = 1) : d163671 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163444 q = 1) (hb : d171278 q = 1) : d163672 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163444 q = 1) (hb : d171279 q = 1) : d163673 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163444 q = 1) (hb : d171280 q = 1) : d163674 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163444 q = 1) (hb : d171281 q = 1) : d163675 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51555 (p : Pattern) (ha : d163444 p = 1) (hb : d171287 p = 1) : d163681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163444 q = 1) (hb : d171282 q = 1) : d163676 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51554 q ha hb
    | true =>
      simp only [d171282, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163444 q = 1) (hb : d171283 q = 1) : d163677 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163444 q = 1) (hb : d171284 q = 1) : d163678 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163444 q = 1) (hb : d171285 q = 1) : d163679 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163444 q = 1) (hb : d171286 q = 1) : d163680 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163444 q = 1) (hb : d171287 q = 1) : d163681 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro51556 (p : Pattern) (ha : d128482 p = 1) (hb : d211412 p = 1) : d128482 p = 1 := by
  have h0 (q : Pattern) (ha : d128482 q = 1) (hb : d211412 q = 1) : d128482 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro51557 (p : Pattern) (ha : d171287 p = 1) (hb : d211412 p = 1) : d171287 p = 1 := by
  have h0 (q : Pattern) (ha : d171287 q = 1) (hb : d211412 q = 1) : d171287 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro51558 (p : Pattern) (ha : d144 p = 1) (hb : d116750 p = 1) : d20893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d116750 q = 1) : d20892 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d116750 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d116750 q = 1) : d20893 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d20893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d20893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51559 (p : Pattern) (ha : d150 p = 1) (hb : d116750 p = 1) : d20899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d116750 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d116750 q = 1) : d20894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
    | true =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d116750 q = 1) : d20895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d116750 q = 1) : d20896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d116750 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d116750 q = 1) : d20897 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d20897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d20897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d116750 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d116750 q = 1) : d20898 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d20898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d20898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d116750 q = 1) : d20899 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d20899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d20899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro51560 (p : Pattern) (ha : d203 p = 1) (hb : d116750 p = 1) : d20912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d116750 q = 1) : d20903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d116750 q = 1) : d20904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d20904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d20904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d116750 q = 1) : d20912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d20912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d20912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51561 (p : Pattern) (ha : d4349 p = 1) (hb : d116750 p = 1) : d150013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d116750 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d116750 q = 1) : d20913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51560 q ha hb
    | true =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d116750 q = 1) : d150002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d116750 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d116750 q = 1) : d150003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d116750 q = 1) : d150011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d150011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d116750 q = 1) : d150012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d150012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d116750 q = 1) : d150013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d150013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51562 (p : Pattern) (ha : d231 p = 1) (hb : d116750 p = 1) : d20932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d116750 q = 1) : d20931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d116750 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d116750 q = 1) : d20932 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d20932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d20932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51563 (p : Pattern) (ha : d237 p = 1) (hb : d116750 p = 1) : d20938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d116750 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d116750 q = 1) : d20933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
    | true =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d116750 q = 1) : d20934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d116750 q = 1) : d20935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d116750 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d116750 q = 1) : d20936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d20936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d20936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d116750 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d116750 q = 1) : d20937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d20937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d20937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d116750 q = 1) : d20938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d20938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d20938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro51564 (p : Pattern) (ha : d243 p = 1) (hb : d116750 p = 1) : d20944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d116750 q = 1) : d20939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51563 q ha hb
    | true =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d116750 q = 1) : d20940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d116750 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d116750 q = 1) : d20941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d20941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d20941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d116750 q = 1) : d20942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d20942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d20942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d116750 q = 1) : d20943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d20943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d20943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d116750 q = 1) : d20944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d20944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d20944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51565 (p : Pattern) (ha : d4359 p = 1) (hb : d116750 p = 1) : d150023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d116750 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d116750 q = 1) : d20945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d20945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51564 q ha hb
    | true =>
      simp only [d244, d20945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d116750 q = 1) : d150019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d150019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d116750 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d116750 q = 1) : d150020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d150020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d116750 q = 1) : d150021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d150021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d116750 q = 1) : d150022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d150022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d116750 q = 1) : d150023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d150023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51566 (p : Pattern) (ha : d156 p = 1) (hb : d116750 p = 1) : d20905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d116750 q = 1) : d20903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d116750 q = 1) : d20904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d20904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d20904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d116750 q = 1) : d20905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d20905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d20905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51567 (p : Pattern) (ha : d51643 p = 1) (hb : d116750 p = 1) : d150001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d116750 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d116750 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d116750 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d116750 q = 1) : d20906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
    | true =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d116750 q = 1) : d149997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d116750 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d116750 q = 1) : d149998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d116750 q = 1) : d149999 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d116750 q = 1) : d150000 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d116750 q = 1) : d150001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d150001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51568 (p : Pattern) (ha : d51646 p = 1) (hb : d116750 p = 1) : d150006 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d116750 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d116750 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d116750 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d116750 q = 1) : d20906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
    | true =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d116750 q = 1) : d149997 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d149997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d116750 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d116750 q = 1) : d149998 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d149998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d116750 q = 1) : d149999 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d149999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d116750 q = 1) : d150000 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d150000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d116750 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d116750 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d116750 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d116750 q = 1) : d20913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51560 q ha hb
    | true =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d116750 q = 1) : d150002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d150002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d116750 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d116750 q = 1) : d150003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d150003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d116750 q = 1) : d150004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d150004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d116750 q = 1) : d150005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d150005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d116750 q = 1) : d150006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d150006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51569 (p : Pattern) (ha : d51652 p = 1) (hb : d116750 p = 1) : d150029 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d116750 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d116750 q = 1) : d150007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51567 q ha hb
    | true =>
      simp only [d51647, d150007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51568 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d116750 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d116750 q = 1) : d150008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d150008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d116750 q = 1) : d150009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d150009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d116750 q = 1) : d150010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d150010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d116750 q = 1) : d150014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d150014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51561 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d116750 q = 1) : d150015 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d150015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d116750 q = 1) : d150016 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d150016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d116750 q = 1) : d150017 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d150017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d116750 q = 1) : d150018 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d150018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d116750 q = 1) : d150024 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d150024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51565 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d116750 q = 1) : d150025 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d150025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d116750 q = 1) : d150026 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d150026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d116750 q = 1) : d150027 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d150027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d116750 q = 1) : d150028 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d150028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d116750 q = 1) : d150029 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d150029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro51570 (p : Pattern) (ha : d284 p = 1) (hb : d116750 p = 1) : d20966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d116750 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d116750 q = 1) : d20906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
    | true =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d116750 q = 1) : d20962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d116750 q = 1) : d20963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d116750 q = 1) : d20964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d116750 q = 1) : d20965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d116750 q = 1) : d20966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d20966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d20966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51571 (p : Pattern) (ha : d291 p = 1) (hb : d116750 p = 1) : d20973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d116750 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d116750 q = 1) : d20906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
    | true =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d116750 q = 1) : d20962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d116750 q = 1) : d20963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d116750 q = 1) : d20964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d116750 q = 1) : d20965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d116750 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d116750 q = 1) : d20913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51560 q ha hb
    | true =>
      simp only [d204, d20913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d116750 q = 1) : d20969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d20969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d20969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d116750 q = 1) : d20970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d20970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d20970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d116750 q = 1) : d20971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d20971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d20971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d116750 q = 1) : d20972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d20972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d20972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d116750 q = 1) : d20973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d20973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d20973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro51572 (p : Pattern) (ha : d397 p = 1) (hb : d116750 p = 1) : d21058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d116750 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d116750 q = 1) : d20906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
    | true =>
      simp only [d157, d20906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d116750 q = 1) : d20962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d20962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d116750 q = 1) : d20963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d20963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d116750 q = 1) : d20964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d20964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d116750 q = 1) : d20965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d20965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d116750 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d116750 q = 1) : d21058 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d21058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d21058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51573 (p : Pattern) (ha : d296 p = 1) (hb : d116750 p = 1) : d20978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d116750 q = 1) : d20903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d116750 q = 1) : d20977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d20977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d20977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d116750 q = 1) : d20978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d20978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d20978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51574 (p : Pattern) (ha : d303 p = 1) (hb : d116750 p = 1) : d20985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d116750 q = 1) : d20983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d20983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d20983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d116750 q = 1) : d20984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d20984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d20984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d116750 q = 1) : d20985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d20985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d20985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51575 (p : Pattern) (ha : d4736 p = 1) (hb : d116750 p = 1) : d21029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d116750 q = 1) : d21026 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d21026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d21026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d116750 q = 1) : d21027 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d21027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d21027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d116750 q = 1) : d21028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d21028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d21028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d116750 q = 1) : d21029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d21029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d21029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51576 (p : Pattern) (ha : d15966 p = 1) (hb : d116750 p = 1) : d20996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d116750 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d116750 q = 1) : d20995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d116750 q = 1) : d20996 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d20996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d20996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro51577 (p : Pattern) (ha : d15972 p = 1) (hb : d116750 p = 1) : d21002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d116750 q = 1) : d20997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51576 q ha hb
    | true =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d116750 q = 1) : d20998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d116750 q = 1) : d20999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d116750 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d116750 q = 1) : d20894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
    | true =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d116750 q = 1) : d20895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d116750 q = 1) : d20896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d116750 q = 1) : d21000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d116750 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d116750 q = 1) : d20897 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d20897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d20897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d116750 q = 1) : d21001 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d21001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d21001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d116750 q = 1) : d21002 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d21002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d21002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro51578 (p : Pattern) (ha : d15978 p = 1) (hb : d116750 p = 1) : d21008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d116750 q = 1) : d21003 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d21003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51577 q ha hb
    | true =>
      simp only [d15973, d21003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d116750 q = 1) : d21004 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d21004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d21004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d116750 q = 1) : d21005 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d21005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d21005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d116750 q = 1) : d21006 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d21006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d21006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d116750 q = 1) : d21007 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d21007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d21007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d116750 q = 1) : d21008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d21008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d21008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51579 (p : Pattern) (ha : d116750 p = 1) (hb : d128195 p = 1) : d150039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d116750 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d116750 q = 1) : d20979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d20979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51573 q ha hb
    | true =>
      simp only [d297, d20979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d116750 q = 1) : d20980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d20980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d20980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d116750 q = 1) : d20981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d20981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d20981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d116750 q = 1) : d20982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d20982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d20982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d116750 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d116750 q = 1) : d20986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d20986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51574 q ha hb
    | true =>
      simp only [d304, d20986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d116750 q = 1) : d20987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d20987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d20987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d116750 q = 1) : d20988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d20988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d20988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d116750 q = 1) : d21009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d21009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51578 q ha hb
    | true =>
      simp only [d15979, d21009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128191 q = 1) : d150035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128191, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d116750 q = 1) : d21030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d21030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51575 q ha hb
    | true =>
      simp only [d4737, d21030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d116750 q = 1) : d21031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d21031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d21031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128192 q = 1) : d150036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128193 q = 1) : d150037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128193, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128194 q = 1) : d150038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128194, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116750 q = 1) (hb : d128195 q = 1) : d150039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128195, d150039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro51580 (p : Pattern) (ha : d376 p = 1) (hb : d116750 p = 1) : d21036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d116750 q = 1) : d20903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d20903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d116750 q = 1) : d20977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d20977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d20977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d116750 q = 1) : d21036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d21036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d21036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51581 (p : Pattern) (ha : d381 p = 1) (hb : d116750 p = 1) : d21041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d116750 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d116750 q = 1) : d20902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d20902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d116750 q = 1) : d20983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d20983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d20983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d116750 q = 1) : d20984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d20984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d20984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d116750 q = 1) : d21041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d21041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d21041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51582 (p : Pattern) (ha : d5355 p = 1) (hb : d116750 p = 1) : d21050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d116750 q = 1) : d21026 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d21026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d21026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d116750 q = 1) : d21027 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d21027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d21027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d116750 q = 1) : d21028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d21028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d21028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d116750 q = 1) : d21050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d21050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d21050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51583 (p : Pattern) (ha : d15985 p = 1) (hb : d116750 p = 1) : d21045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d116750 q = 1) : d21003 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d21003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51577 q ha hb
    | true =>
      simp only [d15973, d21003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d116750 q = 1) : d21004 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d21004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d21004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d116750 q = 1) : d20900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51559 q ha hb
    | true =>
      simp only [d151, d20900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d116750 q = 1) : d20901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d20901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d116750 q = 1) : d21005 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d21005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d21005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d116750 q = 1) : d21006 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d21006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d21006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d116750 q = 1) : d21007 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d21007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d21007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d116750 q = 1) : d21045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d21045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d21045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51584 (p : Pattern) (ha : d116750 p = 1) (hb : d128200 p = 1) : d150044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d116750 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d116750 q = 1) : d20979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d20979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51573 q ha hb
    | true =>
      simp only [d297, d20979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d116750 q = 1) : d20980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d20980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d20980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d116750 q = 1) : d20981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d20981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d20981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d116750 q = 1) : d20982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d20982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d20982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d116750 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d116750 q = 1) : d20986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d20986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51574 q ha hb
    | true =>
      simp only [d304, d20986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d116750 q = 1) : d20987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d20987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d20987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d116750 q = 1) : d20988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d20988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d20988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d116750 q = 1) : d21009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d21009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51578 q ha hb
    | true =>
      simp only [d15979, d21009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51566 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128191 q = 1) : d150035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d128191, d150035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d116750 q = 1) : d21030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d21030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51575 q ha hb
    | true =>
      simp only [d4737, d21030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d116750 q = 1) : d21031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d21031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d21031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128192 q = 1) : d150036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d150036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128193 q = 1) : d150037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128193, d150037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128194 q = 1) : d150038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128194, d150038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d116750 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d116750 q = 1) : d21037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d21037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51580 q ha hb
    | true =>
      simp only [d377, d21037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d116750 q = 1) : d21038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d21038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d21038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d116750 q = 1) : d21039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d21039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d21039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d116750 q = 1) : d21040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d21040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d21040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d116750 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d116750 q = 1) : d21042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d21042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51581 q ha hb
    | true =>
      simp only [d382, d21042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d116750 q = 1) : d21043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d21043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d21043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d116750 q = 1) : d21044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d21044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d21044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d116750 q = 1) : d21046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d21046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51583 q ha hb
    | true =>
      simp only [d15986, d21046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51560 q ha hb
  have h27 (q : Pattern) (ha : d116750 q = 1) (hb : d128196 q = 1) : d150040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d128196, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d116750 q = 1) : d21051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d21051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51582 q ha hb
    | true =>
      simp only [d5356, d21051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d116750 q = 1) : d21052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d21052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d21052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d116750 q = 1) (hb : d128197 q = 1) : d150041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d116750 q = 1) (hb : d128198 q = 1) : d150042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d128198, d150042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d116750 q = 1) (hb : d128199 q = 1) : d150043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d128199, d150043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d116750 q = 1) (hb : d128200 q = 1) : d150044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d150044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro51585 (p : Pattern) (ha : d116750 p = 1) (hb : d128207 p = 1) : d150051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d116750 q = 1) : d21046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d21046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51583 q ha hb
    | true =>
      simp only [d15986, d21046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51560 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128196 q = 1) : d150040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128196, d150040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d116750 q = 1) : d21051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d21051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51582 q ha hb
    | true =>
      simp only [d5356, d21051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d116750 q = 1) : d21052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d21052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d21052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128197 q = 1) : d150041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d150041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128205 q = 1) : d150049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128205, d150049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128206 q = 1) : d150050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128206, d150050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128207 q = 1) : d150051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128207, d150051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51586 (p : Pattern) (ha : d5377 p = 1) (hb : d116750 p = 1) : d21110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d116750 q = 1) : d20939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51563 q ha hb
    | true =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d116750 q = 1) : d20940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d116750 q = 1) : d21107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d21107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d21107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d116750 q = 1) : d21108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d21108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d21108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d116750 q = 1) : d21109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d21109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d21109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d116750 q = 1) : d21110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d21110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d21110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51587 (p : Pattern) (ha : d16004 p = 1) (hb : d116750 p = 1) : d21077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d116750 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d116750 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d116750 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d116750 q = 1) : d21076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d116750 q = 1) : d21077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d21077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d21077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro51588 (p : Pattern) (ha : d16010 p = 1) (hb : d116750 p = 1) : d21083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d116750 q = 1) : d21078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51587 q ha hb
    | true =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d116750 q = 1) : d21079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d116750 q = 1) : d21080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d116750 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d116750 q = 1) : d20933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
    | true =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d116750 q = 1) : d20934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d116750 q = 1) : d20935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d116750 q = 1) : d21081 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d116750 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d116750 q = 1) : d20936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d20936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d20936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d116750 q = 1) : d21082 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d21082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d21082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d116750 q = 1) : d21083 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d21083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d21083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro51589 (p : Pattern) (ha : d16016 p = 1) (hb : d116750 p = 1) : d21089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d116750 q = 1) : d21084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d21084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51588 q ha hb
    | true =>
      simp only [d16011, d21084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d116750 q = 1) : d21085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d21085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d21085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d116750 q = 1) : d20939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51563 q ha hb
    | true =>
      simp only [d238, d20939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d116750 q = 1) : d20940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d20940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d116750 q = 1) : d21086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d21086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d21086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d116750 q = 1) : d21087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d21087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d21087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d116750 q = 1) : d21088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d21088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d21088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d116750 q = 1) : d21089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d21089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d21089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51590 (p : Pattern) (ha : d116750 p = 1) (hb : d128217 p = 1) : d150061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d116750 q = 1) : d21090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d21090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51589 q ha hb
    | true =>
      simp only [d16017, d21090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51564 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128213 q = 1) : d150057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d150057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d150057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d116750 q = 1) : d21111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d21111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51586 q ha hb
    | true =>
      simp only [d5378, d21111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d116750 q = 1) : d21112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d21112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d21112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128214 q = 1) : d150058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d150058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d150058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128215 q = 1) : d150059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d150059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128215, d150059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128216 q = 1) : d150060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d150060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128216, d150060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128217 q = 1) : d150061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d150061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128217, d150061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51591 (p : Pattern) (ha : d116750 p = 1) (hb : d128223 p = 1) : d150067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d116750 q = 1) : d20967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d20967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d20967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51570 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d116750 q = 1) : d20968 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d20968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d20968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d116750 q = 1) : d20974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d20974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51570 q ha hb
    | true =>
      simp only [d292, d20974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51571 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d116750 q = 1) : d20975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d20975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d20975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d116750 q = 1) : d20976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d20976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d20976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128201 q = 1) : d150045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d150045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51579 q ha hb
    | true =>
      simp only [d128201, d150045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51584 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d116750 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d116750 q = 1) : d21059 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d21059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51572 q ha hb
    | true =>
      simp only [d398, d21059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128202 q = 1) : d150046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d150046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d150046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d116750 q = 1) (hb : d128203 q = 1) : d150047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d150047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d150047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128204 q = 1) : d150048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d150048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128204, d150048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128208 q = 1) : d150052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d150052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128208, d150052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51585 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d116750 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128209 q = 1) : d150053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d150053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d150053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128210 q = 1) : d150054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d150054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d150054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128211 q = 1) : d150055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d150055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d150055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d116750 q = 1) (hb : d128212 q = 1) : d150056 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d150056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d150056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d116750 q = 1) (hb : d128218 q = 1) : d150062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d150062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128218, d150062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51590 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d116750 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d116750 q = 1) (hb : d128219 q = 1) : d150063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d150063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d150063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d116750 q = 1) (hb : d128220 q = 1) : d150064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d150064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d150064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116750 q = 1) (hb : d128221 q = 1) : d150065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d150065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d150065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128222 q = 1) : d150066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d150066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d150066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d116750 q = 1) (hb : d128223 q = 1) : d150067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d150067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d150067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro51592 (p : Pattern) (ha : d116750 p = 1) (hb : d128229 p = 1) : d150073 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d116750 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d116750 q = 1) : d150030 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51569 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d116750 q = 1) : d150031 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d116750 q = 1) : d150032 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d116750 q = 1) : d150033 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d116750 q = 1) : d150034 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128224 q = 1) : d150068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d150068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128224, d150068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51591 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128225 q = 1) : d150069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d150069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128225, d150069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128226 q = 1) : d150070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d150070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128226, d150070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116750 q = 1) (hb : d128227 q = 1) : d150071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d150071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128227, d150071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128228 q = 1) : d150072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d150072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128228, d150072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128229 q = 1) : d150073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d150073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d128229, d150073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro51593 (p : Pattern) (ha : d481 p = 1) (hb : d116750 p = 1) : d21135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d116750 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d116750 q = 1) : d20894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
    | true =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d116750 q = 1) : d20895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d116750 q = 1) : d20896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d116750 q = 1) : d21129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d21129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d21129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d116750 q = 1) : d21134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d21134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d21134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d116750 q = 1) : d21135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d21135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d21135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51594 (p : Pattern) (ha : d491 p = 1) (hb : d116750 p = 1) : d21145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116750 q = 1) : d21143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d116750 q = 1) : d21144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d21144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d21144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d116750 q = 1) : d21145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d21145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d21145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51595 (p : Pattern) (ha : d501 p = 1) (hb : d116750 p = 1) : d21155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116750 q = 1) : d21143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d116750 q = 1) : d21144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d21144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d21144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d116750 q = 1) : d21155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d21155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d21155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51596 (p : Pattern) (ha : d644 p = 1) (hb : d116750 p = 1) : d21294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d116750 q = 1) : d21283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d21283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51594 q ha hb
    | true =>
      simp only [d633, d21283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d116750 q = 1) : d21284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d21284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d21284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d116750 q = 1) : d21285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d21285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d21285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d116750 q = 1) : d21286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d21286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d21286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d116750 q = 1) : d21287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d21287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d21287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d116750 q = 1) : d21289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d21289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51595 q ha hb
    | true =>
      simp only [d639, d21289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d116750 q = 1) : d21290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d21290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d21290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d116750 q = 1) : d21291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d21291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d21291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d116750 q = 1) : d21292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d21292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d21292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d116750 q = 1) : d21293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d21293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d21293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d116750 q = 1) : d21294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d21294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d21294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51597 (p : Pattern) (ha : d653 p = 1) (hb : d116750 p = 1) : d21303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d116750 q = 1) : d21289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d21289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51595 q ha hb
    | true =>
      simp only [d639, d21289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d116750 q = 1) : d21290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d21290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d21290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d116750 q = 1) : d21291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d21291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d21291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d116750 q = 1) : d21292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d21292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d21292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d116750 q = 1) : d21293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d21293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d21293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d116750 q = 1) : d21303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d21303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d21303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51598 (p : Pattern) (ha : d683 p = 1) (hb : d116750 p = 1) : d21342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d116750 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d116750 q = 1) : d20933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
    | true =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d116750 q = 1) : d20934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d116750 q = 1) : d20935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d116750 q = 1) : d21332 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d21332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d21332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d116750 q = 1) : d21341 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d21341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d21341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d116750 q = 1) : d21342 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d21342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d21342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51599 (p : Pattern) (ha : d730 p = 1) (hb : d116750 p = 1) : d21398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d116750 q = 1) : d21343 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d21343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51598 q ha hb
    | true =>
      simp only [d684, d21343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d116750 q = 1) : d21344 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d21344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d21344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d116750 q = 1) : d21395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d21395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d21395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d116750 q = 1) : d21396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d21396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d21396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d116750 q = 1) : d21397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d21397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d21397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d116750 q = 1) : d21398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d21398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d21398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51600 (p : Pattern) (ha : d736 p = 1) (hb : d116750 p = 1) : d21404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d116750 q = 1) : d21399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d21399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51599 q ha hb
    | true =>
      simp only [d731, d21399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d116750 q = 1) : d21400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d21400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d21400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d116750 q = 1) : d21401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d21401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d21401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d116750 q = 1) : d21402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d21402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d21402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d116750 q = 1) : d21403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d21403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d21403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d116750 q = 1) : d21404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d21404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d21404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51601 (p : Pattern) (ha : d16036 p = 1) (hb : d116750 p = 1) : d21131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d116750 q = 1) : d20997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51576 q ha hb
    | true =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d116750 q = 1) : d20998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d116750 q = 1) : d20999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d116750 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d116750 q = 1) : d20894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
    | true =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d116750 q = 1) : d20895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d116750 q = 1) : d20896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d116750 q = 1) : d21000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d116750 q = 1) : d21129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d21129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d21129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d116750 q = 1) : d21130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d21130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d21130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d116750 q = 1) : d21131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d21131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d21131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro51602 (p : Pattern) (ha : d16042 p = 1) (hb : d116750 p = 1) : d21141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d116750 q = 1) : d21139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d116750 q = 1) : d21140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d21140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d21140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d116750 q = 1) : d21141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d21141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d21141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51603 (p : Pattern) (ha : d16048 p = 1) (hb : d116750 p = 1) : d21151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d116750 q = 1) : d21146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51602 q ha hb
    | true =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51594 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d116750 q = 1) : d21147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d116750 q = 1) : d21148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d116750 q = 1) : d21149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d116750 q = 1) : d21150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d116750 q = 1) : d21151 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d21151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d21151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51604 (p : Pattern) (ha : d16051 p = 1) (hb : d116750 p = 1) : d21154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d116750 q = 1) : d21139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d116750 q = 1) : d21140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d21140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d21140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d116750 q = 1) : d21154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d21154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d21154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51605 (p : Pattern) (ha : d16057 p = 1) (hb : d116750 p = 1) : d21161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d116750 q = 1) : d21146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51602 q ha hb
    | true =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51594 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d116750 q = 1) : d21147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d116750 q = 1) : d21148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d116750 q = 1) : d21149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d116750 q = 1) : d21150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d116750 q = 1) : d21156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d21156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51604 q ha hb
    | true =>
      simp only [d16052, d21156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51595 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d116750 q = 1) : d21157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d21157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d21157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d116750 q = 1) : d21158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d21158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d21158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d116750 q = 1) : d21159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d21159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d21159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d116750 q = 1) : d21160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d21160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d21160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d116750 q = 1) : d21161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d21161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d21161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51606 (p : Pattern) (ha : d16143 p = 1) (hb : d116750 p = 1) : d21288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d116750 q = 1) : d21146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51602 q ha hb
    | true =>
      simp only [d16043, d21146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51594 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d116750 q = 1) : d21147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d21147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d116750 q = 1) : d21148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d21148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d116750 q = 1) : d21149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d21149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d116750 q = 1) : d21150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d21150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d116750 q = 1) : d21283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d21283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51594 q ha hb
    | true =>
      simp only [d633, d21283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d116750 q = 1) : d21284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d21284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d21284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d116750 q = 1) : d21285 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d21285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d21285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d116750 q = 1) : d21286 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d21286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d21286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d116750 q = 1) : d21287 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d21287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d21287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d116750 q = 1) : d21288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d21288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d21288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51607 (p : Pattern) (ha : d514 p = 1) (hb : d116750 p = 1) : d21168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116750 q = 1) : d21143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d116750 q = 1) : d21167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d21167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d21167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d116750 q = 1) : d21168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d21168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d21168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51608 (p : Pattern) (ha : d524 p = 1) (hb : d116750 p = 1) : d21178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d116750 q = 1) : d21176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d21176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d21176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d116750 q = 1) : d21177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d21177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d21177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d116750 q = 1) : d21178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d21178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d21178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51609 (p : Pattern) (ha : d16062 p = 1) (hb : d116750 p = 1) : d21166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d116750 q = 1) : d21139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d116750 q = 1) : d21165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d21165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d21165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d116750 q = 1) : d21166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d21166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d21166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51610 (p : Pattern) (ha : d16069 p = 1) (hb : d116750 p = 1) : d21175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d116750 q = 1) : d21173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d21173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d21173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d116750 q = 1) : d21174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d21174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d21174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d116750 q = 1) : d21175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d21175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d21175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51611 (p : Pattern) (ha : d9457 p = 1) (hb : d116750 p = 1) : d20989 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d317 q = 1) : d317 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9457 q = 1) (hb : d116750 q = 1) : d20989 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9457, d116750, d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9457, d116750, d20989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51612 (p : Pattern) (ha : d16077 p = 1) (hb : d116750 p = 1) : d21194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d116750 q = 1) : d21191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d116750 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16076 q = 1) (hb : d116750 q = 1) : d21193 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d21193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16076, d21193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16077 q = 1) (hb : d116750 q = 1) : d21194 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d21194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16077, d21194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51613 (p : Pattern) (ha : d16081 p = 1) (hb : d116750 p = 1) : d21198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d116750 q = 1) : d5453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d5453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d5454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d116750 q = 1) : d20995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d20995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d116750 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d116750 q = 1) : d21198 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d21198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d21198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51614 (p : Pattern) (ha : d16087 p = 1) (hb : d116750 p = 1) : d21204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d116750 q = 1) : d21195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d21195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51612 q ha hb
    | true =>
      simp only [d16078, d21195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51576 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d116750 q = 1) : d21196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d21196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d21196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d116750 q = 1) : d21197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d21197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d21197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d116750 q = 1) : d21199 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d21199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51576 q ha hb
    | true =>
      simp only [d16082, d21199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51613 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d116750 q = 1) : d21200 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d21200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d21200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d116750 q = 1) : d21201 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d21201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d21201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d116750 q = 1) : d21202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d21202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d21202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d116750 q = 1) : d20997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51576 q ha hb
    | true =>
      simp only [d15967, d20997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d116750 q = 1) : d20998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d20998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d116750 q = 1) : d20999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d20999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d116750 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d116750 q = 1) : d20894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51558 q ha hb
    | true =>
      simp only [d145, d20894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d116750 q = 1) : d20895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d20895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d116750 q = 1) : d20896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d20896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d116750 q = 1) : d21000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d21000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d116750 q = 1) : d21203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d21203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d21203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d116750 q = 1) : d21204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d21204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d21204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro51615 (p : Pattern) (ha : d16093 p = 1) (hb : d116750 p = 1) : d21210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d116750 q = 1) : d21205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d21205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51614 q ha hb
    | true =>
      simp only [d16088, d21205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d116750 q = 1) : d21206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d21206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d21206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d116750 q = 1) : d21207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d21207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d21207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d116750 q = 1) : d21208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d21208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d21208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d116750 q = 1) : d21209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d21209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d21209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d116750 q = 1) : d21210 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d21210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d21210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51616 (p : Pattern) (ha : d16114 p = 1) (hb : d116750 p = 1) : d21251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d116750 q = 1) : d21248 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d21248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d21248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d116750 q = 1) : d21249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d21249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d21249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d116750 q = 1) : d21250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d21250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d21250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d116750 q = 1) : d21251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d21251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d21251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51617 (p : Pattern) (ha : d116750 p = 1) (hb : d128234 p = 1) : d150078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d116750 q = 1) : d21169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d21169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51609 q ha hb
    | true =>
      simp only [d16063, d21169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51607 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d116750 q = 1) : d21170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d21170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d21170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d116750 q = 1) : d21171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d21171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d21171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d116750 q = 1) : d21172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d21172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d21172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d116750 q = 1) : d21179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d21179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51610 q ha hb
    | true =>
      simp only [d16070, d21179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51608 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d116750 q = 1) : d21180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d21180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d21180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d116750 q = 1) : d21181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d21181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d21181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d116750 q = 1) : d21211 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d21211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51615 q ha hb
    | true =>
      simp only [d16094, d21211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51602 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128230 q = 1) : d150074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128230, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d116750 q = 1) : d21252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d21252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51616 q ha hb
    | true =>
      simp only [d16115, d21252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d116750 q = 1) : d21253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d21253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d21253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128231 q = 1) : d150075 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128232 q = 1) : d150076 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128232, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128233 q = 1) : d150077 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128233, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128234 q = 1) : d150078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d150078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128234, d150078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51618 (p : Pattern) (ha : d610 p = 1) (hb : d116750 p = 1) : d21259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d116750 q = 1) : d21143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d21143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d116750 q = 1) : d21167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d21167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d21167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d116750 q = 1) : d21259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d21259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d21259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51619 (p : Pattern) (ha : d616 p = 1) (hb : d116750 p = 1) : d21265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d116750 q = 1) : d21142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d21142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d116750 q = 1) : d21176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d21176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d21176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d116750 q = 1) : d21177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d21177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d21177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d116750 q = 1) : d21265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d21265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d21265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51620 (p : Pattern) (ha : d16121 p = 1) (hb : d116750 p = 1) : d21258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d116750 q = 1) : d21139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d21139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d116750 q = 1) : d21165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d21165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d21165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d116750 q = 1) : d21258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d21258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d21258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51621 (p : Pattern) (ha : d16126 p = 1) (hb : d116750 p = 1) : d21264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d116750 q = 1) : d21136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51593 q ha hb
    | true =>
      simp only [d482, d21136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d116750 q = 1) : d21137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d21137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d116750 q = 1) : d21138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d21138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d116750 q = 1) : d21173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d21173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d21173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d116750 q = 1) : d21174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d21174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d21174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d116750 q = 1) : d21264 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d21264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d21264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51622 (p : Pattern) (ha : d16130 p = 1) (hb : d116750 p = 1) : d21269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d116750 q = 1) : d21205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d21205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51614 q ha hb
    | true =>
      simp only [d16088, d21205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d116750 q = 1) : d21206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d21206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d21206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d116750 q = 1) : d21207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d21207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d21207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d116750 q = 1) : d21208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d21208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d21208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d116750 q = 1) : d21209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d21209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d21209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d116750 q = 1) : d21269 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d21269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d21269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51623 (p : Pattern) (ha : d16135 p = 1) (hb : d116750 p = 1) : d21275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d116750 q = 1) : d21132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51601 q ha hb
    | true =>
      simp only [d16037, d21132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d116750 q = 1) : d21133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d21133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d116750 q = 1) : d21248 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d21248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d21248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d116750 q = 1) : d21249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d21249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d21249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d116750 q = 1) : d21250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d21250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d21250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d116750 q = 1) : d21275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d21275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d21275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51624 (p : Pattern) (ha : d116750 p = 1) (hb : d128239 p = 1) : d150083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d116750 q = 1) : d21169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d21169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51609 q ha hb
    | true =>
      simp only [d16063, d21169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51607 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d116750 q = 1) : d21170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d21170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d21170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d116750 q = 1) : d21171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d21171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d21171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d116750 q = 1) : d21172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d21172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d21172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d116750 q = 1) : d21179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d21179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51610 q ha hb
    | true =>
      simp only [d16070, d21179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51608 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d116750 q = 1) : d21180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d21180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d21180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d116750 q = 1) : d21181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d21181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d21181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d116750 q = 1) : d21211 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d21211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51615 q ha hb
    | true =>
      simp only [d16094, d21211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51602 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128230 q = 1) : d150074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128230, d150074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d116750 q = 1) : d21252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d21252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51616 q ha hb
    | true =>
      simp only [d16115, d21252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d116750 q = 1) : d21253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d21253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d21253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128231 q = 1) : d150075 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d150075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128232 q = 1) : d150076 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128232, d150076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128233 q = 1) : d150077 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128233, d150077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d116750 q = 1) : d21260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d21260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51620 q ha hb
    | true =>
      simp only [d16122, d21260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51618 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d116750 q = 1) : d21261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d21261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d21261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d116750 q = 1) : d21262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d21262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d21262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d116750 q = 1) : d21263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d21263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d21263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d116750 q = 1) : d21266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d21266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51621 q ha hb
    | true =>
      simp only [d16127, d21266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51619 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d116750 q = 1) : d21267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d21267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d21267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d116750 q = 1) : d21268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d21268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d21268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d116750 q = 1) : d21270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d21270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51622 q ha hb
    | true =>
      simp only [d16131, d21270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51604 q ha hb
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128235 q = 1) : d150079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d128235, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d116750 q = 1) : d21276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d21276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51623 q ha hb
    | true =>
      simp only [d16136, d21276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d116750 q = 1) : d21277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d21277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d21277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116750 q = 1) (hb : d128236 q = 1) : d150080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116750 q = 1) (hb : d128237 q = 1) : d150081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d150081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d128237, d150081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116750 q = 1) (hb : d128238 q = 1) : d150082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d150082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d128238, d150082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116750 q = 1) (hb : d128239 q = 1) : d150083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d150083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d150083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro51625 (p : Pattern) (ha : d116750 p = 1) (hb : d128246 p = 1) : d150090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d116750 q = 1) : d21270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d21270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51622 q ha hb
    | true =>
      simp only [d16131, d21270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51604 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128235 q = 1) : d150079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128235, d150079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d116750 q = 1) : d21276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d21276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51623 q ha hb
    | true =>
      simp only [d16136, d21276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d116750 q = 1) : d21277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d21277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d21277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128236 q = 1) : d150080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d150080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128244 q = 1) : d150088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d150088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128244, d150088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128245 q = 1) : d150089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d150089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128245, d150089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128246 q = 1) : d150090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d150090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128246, d150090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51626 (p : Pattern) (ha : d16162 p = 1) (hb : d116750 p = 1) : d21319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d116750 q = 1) : d21314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d116750 q = 1) : d21315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d116750 q = 1) : d21316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d116750 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d116750 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d116750 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16161 q = 1) (hb : d116750 q = 1) : d21318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d21318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16161, d21318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16162 q = 1) (hb : d116750 q = 1) : d21319 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d21319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16162, d21319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro51627 (p : Pattern) (ha : d16166 p = 1) (hb : d116750 p = 1) : d21323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d116750 q = 1) : d5495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d5495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d116750 q = 1) : d5451 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29396 q ha hb
    | true =>
      simp only [d9382, d5451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d116750 q = 1) : d5496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d5496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d116750 q = 1) : d5452 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d5452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d116750 q = 1) : d5497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d5497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d5498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d116750 q = 1) : d21076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d21076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d116750 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d116750 q = 1) : d21323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d21323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d21323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51628 (p : Pattern) (ha : d16172 p = 1) (hb : d116750 p = 1) : d21329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d116750 q = 1) : d21320 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d21320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51626 q ha hb
    | true =>
      simp only [d16163, d21320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51587 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d116750 q = 1) : d21321 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d21321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d21321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d116750 q = 1) : d21322 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d21322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d21322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d116750 q = 1) : d21324 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d21324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51587 q ha hb
    | true =>
      simp only [d16167, d21324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51627 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d116750 q = 1) : d21325 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d21325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d21325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d116750 q = 1) : d21326 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d21326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d21326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d116750 q = 1) : d21327 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d21327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d21327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d116750 q = 1) : d21078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51587 q ha hb
    | true =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d116750 q = 1) : d21079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d116750 q = 1) : d21080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d116750 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d116750 q = 1) : d20933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
    | true =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d116750 q = 1) : d20934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d116750 q = 1) : d20935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d116750 q = 1) : d21081 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d116750 q = 1) : d21328 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d21328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d21328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d116750 q = 1) : d21329 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d21329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d21329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro51629 (p : Pattern) (ha : d16176 p = 1) (hb : d116750 p = 1) : d21334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d116750 q = 1) : d21078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51587 q ha hb
    | true =>
      simp only [d16005, d21078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d116750 q = 1) : d21079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d21079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d116750 q = 1) : d21080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d21080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d116750 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d116750 q = 1) : d20933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51562 q ha hb
    | true =>
      simp only [d232, d20933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d116750 q = 1) : d20934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d20934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d116750 q = 1) : d20935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d20935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d116750 q = 1) : d21081 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d21081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d116750 q = 1) : d21332 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d21332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d21332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d116750 q = 1) : d21333 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d21333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d21333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d116750 q = 1) : d21334 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d21334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d21334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro51630 (p : Pattern) (ha : d16182 p = 1) (hb : d116750 p = 1) : d21340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d116750 q = 1) : d21330 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d21330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51628 q ha hb
    | true =>
      simp only [d16173, d21330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d116750 q = 1) : d21331 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d21331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d21331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d116750 q = 1) : d21335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51629 q ha hb
    | true =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d116750 q = 1) : d21336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d116750 q = 1) : d21337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d21337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d21337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d116750 q = 1) : d21338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d21338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d21338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d116750 q = 1) : d21339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d21339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d21339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d116750 q = 1) : d21340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d21340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d21340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51631 (p : Pattern) (ha : d16186 p = 1) (hb : d116750 p = 1) : d21348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d116750 q = 1) : d21335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51629 q ha hb
    | true =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d116750 q = 1) : d21336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d116750 q = 1) : d21343 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d21343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51598 q ha hb
    | true =>
      simp only [d684, d21343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d116750 q = 1) : d21344 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d21344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d21344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d116750 q = 1) : d21345 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d21345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d21345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d116750 q = 1) : d21346 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d21346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d21346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d116750 q = 1) : d21347 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d21347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d21347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d116750 q = 1) : d21348 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d21348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d21348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51632 (p : Pattern) (ha : d16207 p = 1) (hb : d116750 p = 1) : d21387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d116750 q = 1) : d21335 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51629 q ha hb
    | true =>
      simp only [d16177, d21335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d116750 q = 1) : d21336 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d21336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d116750 q = 1) : d21384 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d21384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d21384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d116750 q = 1) : d21385 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d21385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d21385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d116750 q = 1) : d21386 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d21386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d21386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d116750 q = 1) : d21387 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d21387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d21387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51633 (p : Pattern) (ha : d116750 p = 1) (hb : d128256 p = 1) : d150100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d116750 q = 1) : d21349 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d21349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51630 q ha hb
    | true =>
      simp only [d16187, d21349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51631 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128252 q = 1) : d150096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d150096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d150096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d116750 q = 1) : d21388 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d21388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51632 q ha hb
    | true =>
      simp only [d16208, d21388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d116750 q = 1) : d21389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d21389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d21389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128253 q = 1) : d150097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d150097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d150097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128254 q = 1) : d150098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d150098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128254, d150098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128255 q = 1) : d150099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d150099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128255, d150099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128256 q = 1) : d150100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d150100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128256, d150100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51634 (p : Pattern) (ha : d116750 p = 1) (hb : d128262 p = 1) : d150106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d116750 q = 1) : d21152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d21152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d21152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51603 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d116750 q = 1) : d21153 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d21153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d21153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d116750 q = 1) : d21162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d21162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51603 q ha hb
    | true =>
      simp only [d16058, d21162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51605 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d116750 q = 1) : d21163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d21163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d21163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d116750 q = 1) : d21164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d21164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d21164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128240 q = 1) : d150084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d150084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51617 q ha hb
    | true =>
      simp only [d128240, d150084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51624 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d116750 q = 1) : d21295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d21295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51606 q ha hb
    | true =>
      simp only [d16144, d21295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51596 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128241 q = 1) : d150085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d150085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d150085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128242 q = 1) : d150086 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d150086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d150086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116750 q = 1) (hb : d128243 q = 1) : d150087 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d150087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128243, d150087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128247 q = 1) : d150091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d150091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128247, d150091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51625 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d116750 q = 1) : d21304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d21304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d21304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51597 q ha hb
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128248 q = 1) : d150092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d150092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d150092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128249 q = 1) : d150093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d150093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d150093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128250 q = 1) : d150094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d150094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d150094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128251 q = 1) : d150095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d150095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d150095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116750 q = 1) (hb : d128257 q = 1) : d150101 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d150101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128257, d150101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51633 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d116750 q = 1) : d21405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d21405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d21405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51600 q ha hb
  have h19 (q : Pattern) (ha : d116750 q = 1) (hb : d128258 q = 1) : d150102 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d150102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d150102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116750 q = 1) (hb : d128259 q = 1) : d150103 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d150103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d150103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116750 q = 1) (hb : d128260 q = 1) : d150104 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d150104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d150104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116750 q = 1) (hb : d128261 q = 1) : d150105 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d150105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d150105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128262 q = 1) : d150106 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d150106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d150106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51635 (p : Pattern) (ha : d116750 p = 1) (hb : d128268 p = 1) : d150112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116750 q = 1) (hb : d128263 q = 1) : d150107 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d150107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128263, d150107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51634 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128264 q = 1) : d150108 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d150108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128264, d150108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116750 q = 1) (hb : d128265 q = 1) : d150109 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d150109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128265, d150109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116750 q = 1) (hb : d128266 q = 1) : d150110 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d150110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128266, d150110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128267 q = 1) : d150111 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d150111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128267, d150111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128268 q = 1) : d150112 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d150112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128268, d150112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51636 (p : Pattern) (ha : d758 p = 1) (hb : d116750 p = 1) : d21420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d755 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d757 q = 1) (hb : d116750 q = 1) : d757 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d758 q = 1) (hb : d116750 q = 1) : d21420 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d21420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d758, d21420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51637 (p : Pattern) (ha : d773 p = 1) (hb : d116750 p = 1) : d21434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d116750 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d763 q = 1) (hb : d116750 q = 1) : d21424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51636 q ha hb
    | true =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d764 q = 1) (hb : d116750 q = 1) : d21425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d765 q = 1) (hb : d116750 q = 1) : d21426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d767 q = 1) (hb : d116750 q = 1) : d21428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d21428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d767, d21428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d772 q = 1) (hb : d116750 q = 1) : d21433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d21433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d772, d21433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d773 q = 1) (hb : d116750 q = 1) : d21434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d21434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d773, d21434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51638 (p : Pattern) (ha : d783 p = 1) (hb : d116750 p = 1) : d21444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116750 q = 1) : d21442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d116750 q = 1) : d21443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d21443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d21443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d116750 q = 1) : d21444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d21444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d21444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51639 (p : Pattern) (ha : d793 p = 1) (hb : d116750 p = 1) : d21454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116750 q = 1) : d21442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d116750 q = 1) : d21443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d21443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d21443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d116750 q = 1) : d21454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d21454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d21454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51640 (p : Pattern) (ha : d950 p = 1) (hb : d116750 p = 1) : d21597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d116750 q = 1) : d21586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d21586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51638 q ha hb
    | true =>
      simp only [d939, d21586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d116750 q = 1) : d21587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d21587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d21587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d116750 q = 1) : d21588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d21588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d21588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d116750 q = 1) : d21589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d21589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d21589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d116750 q = 1) : d21590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d21590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d21590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d116750 q = 1) : d21592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d21592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51639 q ha hb
    | true =>
      simp only [d945, d21592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d116750 q = 1) : d21593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d21593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d21593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d116750 q = 1) : d21594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d21594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d21594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d116750 q = 1) : d21595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d21595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d21595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d116750 q = 1) : d21596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d21596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d21596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d116750 q = 1) : d21597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d21597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d21597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51641 (p : Pattern) (ha : d959 p = 1) (hb : d116750 p = 1) : d21606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d116750 q = 1) : d21592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d21592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51639 q ha hb
    | true =>
      simp only [d945, d21592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d116750 q = 1) : d21593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d21593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d21593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d116750 q = 1) : d21594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d21594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d21594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d116750 q = 1) : d21595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d21595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d21595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d116750 q = 1) : d21596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d21596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d21596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d116750 q = 1) : d21606 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d21606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d21606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51642 (p : Pattern) (ha : d981 p = 1) (hb : d116750 p = 1) : d21633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d975 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d980 q = 1) (hb : d116750 q = 1) : d980 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d981 q = 1) (hb : d116750 q = 1) : d21633 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d21633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d981, d21633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51643 (p : Pattern) (ha : d1005 p = 1) (hb : d116750 p = 1) : d21655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d116750 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d987 q = 1) (hb : d116750 q = 1) : d21637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51642 q ha hb
    | true =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d988 q = 1) (hb : d116750 q = 1) : d21638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d989 q = 1) (hb : d116750 q = 1) : d21639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d995 q = 1) (hb : d116750 q = 1) : d21645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d21645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d995, d21645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1004 q = 1) (hb : d116750 q = 1) : d21654 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d21654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1004, d21654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1005 q = 1) (hb : d116750 q = 1) : d21655 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d21655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1005, d21655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro51644 (p : Pattern) (ha : d1063 p = 1) (hb : d116750 p = 1) : d21715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d116750 q = 1) : d21656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d21656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51643 q ha hb
    | true =>
      simp only [d1006, d21656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d116750 q = 1) : d21657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d21657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d21657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d116750 q = 1) : d21712 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d21712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d21712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d116750 q = 1) : d21713 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d21713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d21713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d116750 q = 1) : d21714 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d21714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d21714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d116750 q = 1) : d21715 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d21715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d21715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51645 (p : Pattern) (ha : d1069 p = 1) (hb : d116750 p = 1) : d21721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d116750 q = 1) : d21716 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d21716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51644 q ha hb
    | true =>
      simp only [d1064, d21716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d116750 q = 1) : d21717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d21717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d21717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d116750 q = 1) : d21718 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d21718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d21718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d116750 q = 1) : d21719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d21719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d21719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d116750 q = 1) : d21720 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d21720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d21720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d116750 q = 1) : d21721 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d21721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d21721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51646 (p : Pattern) (ha : d16227 p = 1) (hb : d116750 p = 1) : d21419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d116750 q = 1) : d21191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12750 q = 1) (hb : d116750 q = 1) : d21418 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16227 q = 1) (hb : d116750 q = 1) : d21419 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d21419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16227, d21419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro51647 (p : Pattern) (ha : d16233 p = 1) (hb : d116750 p = 1) : d21430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d116750 q = 1) : d21421 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d21421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51646 q ha hb
    | true =>
      simp only [d16228, d21421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51636 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d116750 q = 1) : d21422 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d21422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d21422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d116750 q = 1) : d21423 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d21423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d21423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d116750 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d763 q = 1) (hb : d116750 q = 1) : d21424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51636 q ha hb
    | true =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d764 q = 1) (hb : d116750 q = 1) : d21425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d765 q = 1) (hb : d116750 q = 1) : d21426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16231 q = 1) (hb : d116750 q = 1) : d21427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d21427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d21427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d767 q = 1) (hb : d116750 q = 1) : d21428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d21428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d767, d21428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16232 q = 1) (hb : d116750 q = 1) : d21429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d21429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16232, d21429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16233 q = 1) (hb : d116750 q = 1) : d21430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d21430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16233, d21430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro51648 (p : Pattern) (ha : d16239 p = 1) (hb : d116750 p = 1) : d21440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d116750 q = 1) : d21438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d116750 q = 1) : d21439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d21439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d21439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d116750 q = 1) : d21440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d21440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d21440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51649 (p : Pattern) (ha : d16245 p = 1) (hb : d116750 p = 1) : d21450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d116750 q = 1) : d21445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51648 q ha hb
    | true =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51638 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d116750 q = 1) : d21446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d116750 q = 1) : d21447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d116750 q = 1) : d21448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d116750 q = 1) : d21449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d116750 q = 1) : d21450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d21450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d21450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51650 (p : Pattern) (ha : d16248 p = 1) (hb : d116750 p = 1) : d21453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d116750 q = 1) : d21438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d116750 q = 1) : d21439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d21439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d21439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d116750 q = 1) : d21453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d21453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d21453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51651 (p : Pattern) (ha : d16254 p = 1) (hb : d116750 p = 1) : d21460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d116750 q = 1) : d21445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51648 q ha hb
    | true =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51638 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d116750 q = 1) : d21446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d116750 q = 1) : d21447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d116750 q = 1) : d21448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d116750 q = 1) : d21449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d116750 q = 1) : d21455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d21455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51650 q ha hb
    | true =>
      simp only [d16249, d21455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51639 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d116750 q = 1) : d21456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d21456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d21456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d116750 q = 1) : d21457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d21457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d21457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d116750 q = 1) : d21458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d21458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d21458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d116750 q = 1) : d21459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d21459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d21459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d116750 q = 1) : d21460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d21460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d21460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51652 (p : Pattern) (ha : d16343 p = 1) (hb : d116750 p = 1) : d21591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d116750 q = 1) : d21445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51648 q ha hb
    | true =>
      simp only [d16240, d21445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51638 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d116750 q = 1) : d21446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d21446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d116750 q = 1) : d21447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d21447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d116750 q = 1) : d21448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d21448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d116750 q = 1) : d21449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d21449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d116750 q = 1) : d21586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d21586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51638 q ha hb
    | true =>
      simp only [d939, d21586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d116750 q = 1) : d21587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d21587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d21587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d116750 q = 1) : d21588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d21588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d21588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d116750 q = 1) : d21589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d21589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d21589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d116750 q = 1) : d21590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d21590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d21590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d116750 q = 1) : d21591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d21591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d21591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51653 (p : Pattern) (ha : d806 p = 1) (hb : d116750 p = 1) : d21467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116750 q = 1) : d21442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d116750 q = 1) : d21466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d21466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d21466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d116750 q = 1) : d21467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d21467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d21467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51654 (p : Pattern) (ha : d816 p = 1) (hb : d116750 p = 1) : d21477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d116750 q = 1) : d21475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d21475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d21475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d116750 q = 1) : d21476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d21476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d21476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d116750 q = 1) : d21477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d21477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d21477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51655 (p : Pattern) (ha : d16259 p = 1) (hb : d116750 p = 1) : d21465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d116750 q = 1) : d21438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d116750 q = 1) : d21464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d21464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d21464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d116750 q = 1) : d21465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d21465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d21465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51656 (p : Pattern) (ha : d16266 p = 1) (hb : d116750 p = 1) : d21474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d116750 q = 1) : d21472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d21472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d21472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d116750 q = 1) : d21473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d21473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d21473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d116750 q = 1) : d21474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d21474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d21474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51657 (p : Pattern) (ha : d9586 p = 1) (hb : d116750 p = 1) : d21182 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d541 q = 1) : d541 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9586 q = 1) (hb : d116750 q = 1) : d21182 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9586, d116750, d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9586, d116750, d21182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51658 (p : Pattern) (ha : d16274 p = 1) (hb : d116750 p = 1) : d21493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d116750 q = 1) : d21484 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d116750 q = 1) : d21485 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9587 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
    | true =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16270 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16271 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16271, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16272 q = 1) (hb : d116750 q = 1) : d21486 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9597 q = 1) (hb : d116750 q = 1) : d21488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d21488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36912 q ha hb
    | true =>
      simp only [d9597, d21488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d116750 q = 1) : d21489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d21489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9599, d21489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14529 q = 1) (hb : d116750 q = 1) : d21490 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d21490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d21490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14530 q = 1) (hb : d116750 q = 1) : d21491 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d21491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14530, d21491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12748 q = 1) (hb : d116750 q = 1) : d21191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12749 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16273 q = 1) (hb : d116750 q = 1) : d21492 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d21492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16273, d21492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16274 q = 1) (hb : d116750 q = 1) : d21493 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d21493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16274, d21493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51659 (p : Pattern) (ha : d16278 p = 1) (hb : d116750 p = 1) : d21497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d116750 q = 1) : d21191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d21191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d21192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12750 q = 1) (hb : d116750 q = 1) : d21418 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d21418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d757 q = 1) (hb : d116750 q = 1) : d757 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16278 q = 1) (hb : d116750 q = 1) : d21497 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d21497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16278, d21497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51660 (p : Pattern) (ha : d16284 p = 1) (hb : d116750 p = 1) : d21503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d116750 q = 1) : d21494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d21494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51658 q ha hb
    | true =>
      simp only [d16275, d21494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51646 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d116750 q = 1) : d21495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d21495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d21495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d116750 q = 1) : d21496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d21496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d21496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d116750 q = 1) : d21498 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d21498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51646 q ha hb
    | true =>
      simp only [d16279, d21498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51659 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d116750 q = 1) : d21499 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d21499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d21499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d116750 q = 1) : d21500 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d21500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d21500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d116750 q = 1) : d21501 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d21501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d21501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d116750 q = 1) : d21421 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d21421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51646 q ha hb
    | true =>
      simp only [d16228, d21421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51636 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d116750 q = 1) : d21422 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d21422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d21422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d116750 q = 1) : d21423 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d21423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d21423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d116750 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d763 q = 1) (hb : d116750 q = 1) : d21424 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51636 q ha hb
    | true =>
      simp only [d763, d21424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d764 q = 1) (hb : d116750 q = 1) : d21425 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d21425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d765 q = 1) (hb : d116750 q = 1) : d21426 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d21426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16231 q = 1) (hb : d116750 q = 1) : d21427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d21427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d21427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16283 q = 1) (hb : d116750 q = 1) : d21502 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d21502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d21502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16284 q = 1) (hb : d116750 q = 1) : d21503 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d21503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16284, d21503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro51661 (p : Pattern) (ha : d16290 p = 1) (hb : d116750 p = 1) : d21509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d116750 q = 1) : d21504 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d21504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51660 q ha hb
    | true =>
      simp only [d16285, d21504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d116750 q = 1) : d21505 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d21505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d21505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d116750 q = 1) : d21506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d21506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d21506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d116750 q = 1) : d21507 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d21507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d21507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d116750 q = 1) : d21508 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d21508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d21508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d116750 q = 1) : d21509 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d21509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d21509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51662 (p : Pattern) (ha : d16314 p = 1) (hb : d116750 p = 1) : d21554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d116750 q = 1) : d21551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d21551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d21551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d116750 q = 1) : d21552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d21552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d21552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d116750 q = 1) : d21553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d21553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d21553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d116750 q = 1) : d21554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d21554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d21554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51663 (p : Pattern) (ha : d116750 p = 1) (hb : d128274 p = 1) : d150118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d116750 q = 1) : d21468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d21468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51655 q ha hb
    | true =>
      simp only [d16260, d21468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51653 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d116750 q = 1) : d21469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d21469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d21469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d116750 q = 1) : d21470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d21470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d21470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d116750 q = 1) : d21471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d21471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d21471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d116750 q = 1) : d21478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d21478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51656 q ha hb
    | true =>
      simp only [d16267, d21478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51654 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d116750 q = 1) : d21479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d21479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d21479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d116750 q = 1) : d21480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d21480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d21480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d116750 q = 1) : d21510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d21510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51661 q ha hb
    | true =>
      simp only [d16291, d21510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51648 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128270 q = 1) : d150114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128270, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d116750 q = 1) : d21555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d21555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51662 q ha hb
    | true =>
      simp only [d16315, d21555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d116750 q = 1) : d21556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d21556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d21556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128271 q = 1) : d150115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128272 q = 1) : d150116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128272, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128273 q = 1) : d150117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128273, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128274 q = 1) : d150118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128274, d150118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51664 (p : Pattern) (ha : d916 p = 1) (hb : d116750 p = 1) : d21562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d116750 q = 1) : d21442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d21442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d116750 q = 1) : d21466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d21466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d21466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d116750 q = 1) : d21562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d21562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d21562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51665 (p : Pattern) (ha : d922 p = 1) (hb : d116750 p = 1) : d21568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d116750 q = 1) : d21441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d21441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d116750 q = 1) : d21475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d21475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d21475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d116750 q = 1) : d21476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d21476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d21476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d116750 q = 1) : d21568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d21568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d21568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51666 (p : Pattern) (ha : d16321 p = 1) (hb : d116750 p = 1) : d21561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d116750 q = 1) : d21438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d21438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d116750 q = 1) : d21464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d21464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d21464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d116750 q = 1) : d21561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d21561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d21561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51667 (p : Pattern) (ha : d16326 p = 1) (hb : d116750 p = 1) : d21567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d116750 q = 1) : d21435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51637 q ha hb
    | true =>
      simp only [d774, d21435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d116750 q = 1) : d21436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d21436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d116750 q = 1) : d21437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d21437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d116750 q = 1) : d21472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d21472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d21472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d116750 q = 1) : d21473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d21473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d21473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d116750 q = 1) : d21567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d21567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d21567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51668 (p : Pattern) (ha : d16330 p = 1) (hb : d116750 p = 1) : d21572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d116750 q = 1) : d21504 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d21504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51660 q ha hb
    | true =>
      simp only [d16285, d21504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d116750 q = 1) : d21505 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d21505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d21505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d116750 q = 1) : d21506 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d21506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d21506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d116750 q = 1) : d21507 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d21507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d21507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d116750 q = 1) : d21508 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d21508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d21508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d116750 q = 1) : d21572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d21572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d21572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51669 (p : Pattern) (ha : d16335 p = 1) (hb : d116750 p = 1) : d21578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d116750 q = 1) : d21431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51647 q ha hb
    | true =>
      simp only [d16234, d21431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d116750 q = 1) : d21432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d21432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d116750 q = 1) : d21551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d21551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d21551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d116750 q = 1) : d21552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d21552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d21552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d116750 q = 1) : d21553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d21553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d21553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d116750 q = 1) : d21578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d21578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d21578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51670 (p : Pattern) (ha : d116750 p = 1) (hb : d128279 p = 1) : d150123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d116750 q = 1) : d21468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d21468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51655 q ha hb
    | true =>
      simp only [d16260, d21468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51653 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d116750 q = 1) : d21469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d21469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d21469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d116750 q = 1) : d21470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d21470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d21470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d116750 q = 1) : d21471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d21471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d21471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d116750 q = 1) : d21478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d21478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51656 q ha hb
    | true =>
      simp only [d16267, d21478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51654 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d116750 q = 1) : d21479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d21479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d21479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d116750 q = 1) : d21480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d21480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d21480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d116750 q = 1) : d21510 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d21510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51661 q ha hb
    | true =>
      simp only [d16291, d21510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51648 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128270 q = 1) : d150114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128270, d150114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d116750 q = 1) : d21555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d21555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51662 q ha hb
    | true =>
      simp only [d16315, d21555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d116750 q = 1) : d21556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d21556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d21556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128271 q = 1) : d150115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d150115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128272 q = 1) : d150116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128272, d150116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128273 q = 1) : d150117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128273, d150117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d116750 q = 1) : d21563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d21563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51666 q ha hb
    | true =>
      simp only [d16322, d21563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51664 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d116750 q = 1) : d21564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d21564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d21564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d116750 q = 1) : d21565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d21565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d21565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d116750 q = 1) : d21566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d21566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d21566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d116750 q = 1) : d21569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d21569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51667 q ha hb
    | true =>
      simp only [d16327, d21569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51665 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d116750 q = 1) : d21570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d21570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d21570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d116750 q = 1) : d21571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d21571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d21571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d116750 q = 1) : d21573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d21573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51668 q ha hb
    | true =>
      simp only [d16331, d21573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51650 q ha hb
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128275 q = 1) : d150119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d128275, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d116750 q = 1) : d21579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d21579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51669 q ha hb
    | true =>
      simp only [d16336, d21579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d116750 q = 1) : d21580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d21580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d21580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116750 q = 1) (hb : d128276 q = 1) : d150120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116750 q = 1) (hb : d128277 q = 1) : d150121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d128277, d150121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116750 q = 1) (hb : d128278 q = 1) : d150122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d128278, d150122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116750 q = 1) (hb : d128279 q = 1) : d150123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d150123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro51671 (p : Pattern) (ha : d116750 p = 1) (hb : d128286 p = 1) : d150130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d116750 q = 1) : d21573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d21573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51668 q ha hb
    | true =>
      simp only [d16331, d21573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51650 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128275 q = 1) : d150119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128275, d150119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d116750 q = 1) : d21579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d21579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51669 q ha hb
    | true =>
      simp only [d16336, d21579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d116750 q = 1) : d21580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d21580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d21580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128276 q = 1) : d150120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d150120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128284 q = 1) : d150128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128284, d150128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128285 q = 1) : d150129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128285, d150129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128286 q = 1) : d150130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d150130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128286, d150130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51672 (p : Pattern) (ha : d16362 p = 1) (hb : d116750 p = 1) : d21622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d116750 q = 1) : d21612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d116750 q = 1) : d21613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d116750 q = 1) : d21614 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d116750 q = 1) : d21615 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51657 q ha hb
    | true =>
      simp only [d9587, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16357, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9589 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9589, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16358 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16358, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16359 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16359, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16360 q = 1) (hb : d116750 q = 1) : d21616 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16360, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d116750 q = 1) : d21617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d21617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d21617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36912 q ha hb
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d116750 q = 1) : d21488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d21488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36912 q ha hb
    | true =>
      simp only [d9597, d21488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14645 q = 1) (hb : d116750 q = 1) : d21618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d21618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14645, d21618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9599 q = 1) (hb : d116750 q = 1) : d21489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d21489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9599, d21489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14646 q = 1) (hb : d116750 q = 1) : d21619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d21619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14646, d21619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14647 q = 1) (hb : d116750 q = 1) : d21620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d21620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14647, d21620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d116750 q = 1) : d21314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12859 q = 1) (hb : d116750 q = 1) : d21315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12860 q = 1) (hb : d116750 q = 1) : d21316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12861 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16361 q = 1) (hb : d116750 q = 1) : d21621 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d21621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16361, d21621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16362 q = 1) (hb : d116750 q = 1) : d21622 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d21622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16362, d21622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro51673 (p : Pattern) (ha : d16363 p = 1) (hb : d116750 p = 1) : d21624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51611 q ha hb
    | true =>
      simp only [d9458, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d116750 q = 1) : d21314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d116750 q = 1) : d21315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d116750 q = 1) : d21316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12862 q = 1) (hb : d116750 q = 1) : d21623 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16363 q = 1) (hb : d116750 q = 1) : d21624 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d21624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16363, d21624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro51674 (p : Pattern) (ha : d16367 p = 1) (hb : d116750 p = 1) : d21628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d116750 q = 1) : d21314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d21314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d116750 q = 1) : d21189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29441 q ha hb
    | true =>
      simp only [d9468, d21189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d116750 q = 1) : d21315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d21315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d116750 q = 1) : d21190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d21190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d116750 q = 1) : d21316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d21316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d21317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12862 q = 1) (hb : d116750 q = 1) : d21623 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d21623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d980 q = 1) (hb : d116750 q = 1) : d980 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16367 q = 1) (hb : d116750 q = 1) : d21628 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d21628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16367, d21628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro51675 (p : Pattern) (ha : d16377 p = 1) (hb : d116750 p = 1) : d21642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d116750 q = 1) : d21625 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d21625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51672 q ha hb
    | true =>
      simp only [d16364, d21625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51673 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d116750 q = 1) : d21626 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d21626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d21626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d116750 q = 1) : d21627 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d21627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d21627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d116750 q = 1) : d21629 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d21629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51673 q ha hb
    | true =>
      simp only [d16368, d21629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51674 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d116750 q = 1) : d21630 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d21630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d21630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d116750 q = 1) : d21631 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d21631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d21631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d116750 q = 1) : d21632 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d21632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d21632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d116750 q = 1) : d21634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d21634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51673 q ha hb
    | true =>
      simp only [d16372, d21634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51642 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d116750 q = 1) : d21635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d21635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d21635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d116750 q = 1) : d21636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d21636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d21636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d116750 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d987 q = 1) (hb : d116750 q = 1) : d21637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51642 q ha hb
    | true =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d988 q = 1) (hb : d116750 q = 1) : d21638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d989 q = 1) (hb : d116750 q = 1) : d21639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16375 q = 1) (hb : d116750 q = 1) : d21640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d21640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d21640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16376 q = 1) (hb : d116750 q = 1) : d21641 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d21641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d21641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16377 q = 1) (hb : d116750 q = 1) : d21642 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d21642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16377, d21642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro51676 (p : Pattern) (ha : d16381 p = 1) (hb : d116750 p = 1) : d21647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d116750 q = 1) : d21634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d21634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51673 q ha hb
    | true =>
      simp only [d16372, d21634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51642 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d116750 q = 1) : d21635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d21635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d21635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d116750 q = 1) : d21636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d21636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d21636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d116750 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d987 q = 1) (hb : d116750 q = 1) : d21637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51642 q ha hb
    | true =>
      simp only [d987, d21637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d988 q = 1) (hb : d116750 q = 1) : d21638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d21638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d989 q = 1) (hb : d116750 q = 1) : d21639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d21639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16375 q = 1) (hb : d116750 q = 1) : d21640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d21640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d21640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d995 q = 1) (hb : d116750 q = 1) : d21645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d21645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d995, d21645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16380 q = 1) (hb : d116750 q = 1) : d21646 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d21646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16380, d21646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16381 q = 1) (hb : d116750 q = 1) : d21647 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d21647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16381, d21647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro51677 (p : Pattern) (ha : d16387 p = 1) (hb : d116750 p = 1) : d21653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d116750 q = 1) : d21643 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d21643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51675 q ha hb
    | true =>
      simp only [d16378, d21643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d116750 q = 1) : d21644 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d21644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d21644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d116750 q = 1) : d21648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51676 q ha hb
    | true =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d116750 q = 1) : d21649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d116750 q = 1) : d21650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d21650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d21650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d116750 q = 1) : d21651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d21651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d21651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d116750 q = 1) : d21652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d21652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d21652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d116750 q = 1) : d21653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d21653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d21653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51678 (p : Pattern) (ha : d16391 p = 1) (hb : d116750 p = 1) : d21661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d116750 q = 1) : d21648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51676 q ha hb
    | true =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d116750 q = 1) : d21649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d116750 q = 1) : d21656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d21656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51643 q ha hb
    | true =>
      simp only [d1006, d21656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d116750 q = 1) : d21657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d21657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d21657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d116750 q = 1) : d21658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d21658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d21658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d116750 q = 1) : d21659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d21659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d21659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d116750 q = 1) : d21660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d21660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d21660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d116750 q = 1) : d21661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d21661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d21661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51679 (p : Pattern) (ha : d16417 p = 1) (hb : d116750 p = 1) : d21704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d116750 q = 1) : d21648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51676 q ha hb
    | true =>
      simp only [d16382, d21648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d116750 q = 1) : d21649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d21649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d116750 q = 1) : d21701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d21701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d21701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d116750 q = 1) : d21702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d21702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d21702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d116750 q = 1) : d21703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d21703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d21703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d116750 q = 1) : d21704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d21704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d21704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51680 (p : Pattern) (ha : d116750 p = 1) (hb : d128296 p = 1) : d150140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d116750 q = 1) : d21662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d21662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51677 q ha hb
    | true =>
      simp only [d16392, d21662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51678 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128292 q = 1) : d150136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d150136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d150136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d116750 q = 1) : d21705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d21705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51679 q ha hb
    | true =>
      simp only [d16418, d21705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d116750 q = 1) : d21706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d21706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d21706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128293 q = 1) : d150137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d150137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d150137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128294 q = 1) : d150138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d150138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128294, d150138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128295 q = 1) : d150139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d150139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128295, d150139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128296 q = 1) : d150140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d150140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128296, d150140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51681 (p : Pattern) (ha : d116750 p = 1) (hb : d128302 p = 1) : d150146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d116750 q = 1) : d21451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d21451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d21451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51649 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d116750 q = 1) : d21452 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d21452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d21452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d116750 q = 1) : d21461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d21461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51649 q ha hb
    | true =>
      simp only [d16255, d21461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51651 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d116750 q = 1) : d21462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d21462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d21462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d116750 q = 1) : d21463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d21463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d21463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128280 q = 1) : d150124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51663 q ha hb
    | true =>
      simp only [d128280, d150124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51670 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d116750 q = 1) : d21598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d21598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51652 q ha hb
    | true =>
      simp only [d16344, d21598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51640 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128281 q = 1) : d150125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d150125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128282 q = 1) : d150126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d150126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d150126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116750 q = 1) (hb : d128283 q = 1) : d150127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d150127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128283, d150127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128287 q = 1) : d150131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d150131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128287, d150131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51671 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d116750 q = 1) : d21607 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d21607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d21607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51641 q ha hb
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128288 q = 1) : d150132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d150132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d150132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128289 q = 1) : d150133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d150133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d150133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128290 q = 1) : d150134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d150134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d150134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128291 q = 1) : d150135 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d150135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d150135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116750 q = 1) (hb : d128297 q = 1) : d150141 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d150141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128297, d150141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51680 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d116750 q = 1) : d21722 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d21722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d21722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51645 q ha hb
  have h19 (q : Pattern) (ha : d116750 q = 1) (hb : d128298 q = 1) : d150142 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d150142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d150142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116750 q = 1) (hb : d128299 q = 1) : d150143 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d150143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d150143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116750 q = 1) (hb : d128300 q = 1) : d150144 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d150144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d150144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116750 q = 1) (hb : d128301 q = 1) : d150145 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d150145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d150145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128302 q = 1) : d150146 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d150146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d150146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51682 (p : Pattern) (ha : d116750 p = 1) (hb : d128308 p = 1) : d150152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116750 q = 1) (hb : d128303 q = 1) : d150147 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d150147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128303, d150147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51681 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128304 q = 1) : d150148 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d150148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128304, d150148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116750 q = 1) (hb : d128305 q = 1) : d150149 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d150149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128305, d150149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116750 q = 1) (hb : d128306 q = 1) : d150150 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d150150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128306, d150150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128307 q = 1) : d150151 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d150151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128307, d150151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128308 q = 1) : d150152 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d150152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128308, d150152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51683 (p : Pattern) (ha : d14773 p = 1) (hb : d116750 p = 1) : d21771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d116750 q = 1) : d21766 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
    | true =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d116750 q = 1) : d21767 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d116750 q = 1) : d21768 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d21768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d21768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d116750 q = 1) : d21769 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d21769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d21769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d116750 q = 1) : d21770 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d21770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d21770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d116750 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14773 q = 1) (hb : d116750 q = 1) : d21771 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d21771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14773, d21771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51684 (p : Pattern) (ha : d14778 p = 1) (hb : d116750 p = 1) : d21777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d116750 q = 1) : d21776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d116750 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14778 q = 1) (hb : d116750 q = 1) : d21777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d21777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14778, d21777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51685 (p : Pattern) (ha : d9788 p = 1) (hb : d116750 p = 1) : d21741 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1098 q = 1) : d1098 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9788 q = 1) (hb : d116750 q = 1) : d21741 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9788, d116750, d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9788, d116750, d21741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51686 (p : Pattern) (ha : d16442 p = 1) (hb : d116750 p = 1) : d21753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9789 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
    | true =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16438 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16438, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16439 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16439, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16440 q = 1) (hb : d116750 q = 1) : d21746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16440, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9778 q = 1) (hb : d116750 q = 1) : d21748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
    | true =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d116750 q = 1) : d21749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14758 q = 1) (hb : d116750 q = 1) : d21750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d21750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d21750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14759 q = 1) (hb : d116750 q = 1) : d21751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d21751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14759, d21751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14763 q = 1) (hb : d116750 q = 1) : d13027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14764 q = 1) (hb : d116750 q = 1) : d13028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16441 q = 1) (hb : d116750 q = 1) : d21752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d21752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16441, d21752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16442 q = 1) (hb : d116750 q = 1) : d21753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d21753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16442, d21753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51687 (p : Pattern) (ha : d16443 p = 1) (hb : d116750 p = 1) : d21761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14763 q = 1) (hb : d116750 q = 1) : d13027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14764 q = 1) (hb : d116750 q = 1) : d13028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d14765 q = 1) (hb : d116750 q = 1) : d21760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d21760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14765, d21760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16443 q = 1) (hb : d116750 q = 1) : d21761 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d21761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16443, d21761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51688 (p : Pattern) (ha : d16456 p = 1) (hb : d116750 p = 1) : d21783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d116750 q = 1) : d21762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
    | true =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d116750 q = 1) : d21763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d116750 q = 1) : d21764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d116750 q = 1) : d21772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51683 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d116750 q = 1) : d21773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d116750 q = 1) : d21774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d116750 q = 1) : d21775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d116750 q = 1) : d21778 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d21778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16451, d21778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51684 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d116750 q = 1) : d21779 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d21779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d21779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d116750 q = 1) : d21780 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d21780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d21780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d116750 q = 1) : d21781 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d21781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d21781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d116750 q = 1) : d21782 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d21782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d21782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d116750 q = 1) : d21783 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d21783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d21783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51689 (p : Pattern) (ha : d16460 p = 1) (hb : d116750 p = 1) : d21787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d116750 q = 1) : d21778 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d21778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16451, d21778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51684 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d116750 q = 1) : d21779 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d21779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d21779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d116750 q = 1) : d21780 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d21780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d21780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d116750 q = 1) : d21781 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d21781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d21781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d116750 q = 1) : d21786 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d21786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d21786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d116750 q = 1) : d21787 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d21787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d21787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51690 (p : Pattern) (ha : d16466 p = 1) (hb : d116750 p = 1) : d21793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d116750 q = 1) : d21791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d116750 q = 1) : d21792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d21792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d21792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d116750 q = 1) : d21793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d21793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d21793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51691 (p : Pattern) (ha : d16470 p = 1) (hb : d116750 p = 1) : d21797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d116750 q = 1) : d21795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d116750 q = 1) : d21796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d21796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d21796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d116750 q = 1) : d21797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d21797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d21797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51692 (p : Pattern) (ha : d16476 p = 1) (hb : d116750 p = 1) : d21803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d116750 q = 1) : d21798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d21798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51690 q ha hb
    | true =>
      simp only [d16471, d21798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51691 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d116750 q = 1) : d21799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d21799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d21799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d116750 q = 1) : d21800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d21800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d21800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d116750 q = 1) : d21801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d21801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d21801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d116750 q = 1) : d21802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d21802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d21802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16476 q = 1) (hb : d116750 q = 1) : d21803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16476, d21803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16476, d21803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51693 (p : Pattern) (ha : d16479 p = 1) (hb : d116750 p = 1) : d21806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d116750 q = 1) : d21791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d116750 q = 1) : d21792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d21792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d21792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16479 q = 1) (hb : d116750 q = 1) : d21806 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16479, d21806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16479, d21806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51694 (p : Pattern) (ha : d16480 p = 1) (hb : d116750 p = 1) : d21807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d116750 q = 1) : d21795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d116750 q = 1) : d21796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d21796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d21796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16480 q = 1) (hb : d116750 q = 1) : d21807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16480, d21807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16480, d21807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51695 (p : Pattern) (ha : d16486 p = 1) (hb : d116750 p = 1) : d21813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16471 q = 1) (hb : d116750 q = 1) : d21798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16471, d21798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51690 q ha hb
    | true =>
      simp only [d16471, d21798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51691 q ha hb
  have h2 (q : Pattern) (ha : d16472 q = 1) (hb : d116750 q = 1) : d21799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16472, d21799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16472, d21799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16473 q = 1) (hb : d116750 q = 1) : d21800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16473, d21800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16473, d21800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16474 q = 1) (hb : d116750 q = 1) : d21801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16474, d21801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16474, d21801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16475 q = 1) (hb : d116750 q = 1) : d21802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16475, d21802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16475, d21802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16481 q = 1) (hb : d116750 q = 1) : d21808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d21808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51693 q ha hb
    | true =>
      simp only [d16481, d21808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51694 q ha hb
  have h7 (q : Pattern) (ha : d16482 q = 1) (hb : d116750 q = 1) : d21809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d21809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d21809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16483 q = 1) (hb : d116750 q = 1) : d21810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d21810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16483, d21810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16484 q = 1) (hb : d116750 q = 1) : d21811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d21811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d21811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16485 q = 1) (hb : d116750 q = 1) : d21812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d21812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d21812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16486 q = 1) (hb : d116750 q = 1) : d21813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16486, d21813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16486, d21813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51696 (p : Pattern) (ha : d16527 p = 1) (hb : d116750 p = 1) : d21867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d116750 q = 1) : d21762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
    | true =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d116750 q = 1) : d21763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d116750 q = 1) : d21764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d116750 q = 1) : d21772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51683 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d116750 q = 1) : d21773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d116750 q = 1) : d21774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d116750 q = 1) : d21775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d116750 q = 1) : d21865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d21865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d21865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d116750 q = 1) : d21866 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d21866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d21866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16527 q = 1) (hb : d116750 q = 1) : d21867 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16527, d21867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16527, d21867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro51697 (p : Pattern) (ha : d16537 p = 1) (hb : d116750 p = 1) : d21877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d116750 q = 1) : d21868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51696 q ha hb
    | true =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d116750 q = 1) : d21869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d116750 q = 1) : d21874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d21874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d21874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d116750 q = 1) : d21875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d21875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d21875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d116750 q = 1) : d21876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d21876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d21876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16537 q = 1) (hb : d116750 q = 1) : d21877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16537, d21877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16537, d21877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51698 (p : Pattern) (ha : d16628 p = 1) (hb : d116750 p = 1) : d22003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16618 q = 1) (hb : d116750 q = 1) : d21993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16618, d21993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51697 q ha hb
    | true =>
      simp only [d16618, d21993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51691 q ha hb
  have h2 (q : Pattern) (ha : d16619 q = 1) (hb : d116750 q = 1) : d21994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16619, d21994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16619, d21994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16620 q = 1) (hb : d116750 q = 1) : d21995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16620, d21995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16620, d21995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16621 q = 1) (hb : d116750 q = 1) : d21996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16621, d21996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16621, d21996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16622 q = 1) (hb : d116750 q = 1) : d21997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16622, d21997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16622, d21997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16623 q = 1) (hb : d116750 q = 1) : d21998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d21998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51691 q ha hb
    | true =>
      simp only [d16623, d21998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16624 q = 1) (hb : d116750 q = 1) : d21999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d21999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d21999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16625 q = 1) (hb : d116750 q = 1) : d22000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d22000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16625, d22000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16626 q = 1) (hb : d116750 q = 1) : d22001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d22001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d22001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16627 q = 1) (hb : d116750 q = 1) : d22002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d22002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d22002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16628 q = 1) (hb : d116750 q = 1) : d22003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16628, d22003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16628, d22003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51699 (p : Pattern) (ha : d16634 p = 1) (hb : d116750 p = 1) : d22009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16623 q = 1) (hb : d116750 q = 1) : d21998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16623, d21998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51691 q ha hb
    | true =>
      simp only [d16623, d21998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16624 q = 1) (hb : d116750 q = 1) : d21999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16624, d21999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16624, d21999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16625 q = 1) (hb : d116750 q = 1) : d22000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16625, d22000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16625, d22000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16626 q = 1) (hb : d116750 q = 1) : d22001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16626, d22001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16626, d22001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16627 q = 1) (hb : d116750 q = 1) : d22002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16627, d22002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16627, d22002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16629 q = 1) (hb : d116750 q = 1) : d22004 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d22004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51694 q ha hb
    | true =>
      simp only [d16629, d22004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16630 q = 1) (hb : d116750 q = 1) : d22005 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d22005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d22005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16631 q = 1) (hb : d116750 q = 1) : d22006 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d22006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16631, d22006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16632 q = 1) (hb : d116750 q = 1) : d22007 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d22007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d22007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16633 q = 1) (hb : d116750 q = 1) : d22008 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d22008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d22008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16634 q = 1) (hb : d116750 q = 1) : d22009 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16634, d22009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16634, d22009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51700 (p : Pattern) (ha : d16643 p = 1) (hb : d116750 p = 1) : d22018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16629 q = 1) (hb : d116750 q = 1) : d22004 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16629, d22004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51694 q ha hb
    | true =>
      simp only [d16629, d22004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16630 q = 1) (hb : d116750 q = 1) : d22005 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16630, d22005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16630, d22005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16631 q = 1) (hb : d116750 q = 1) : d22006 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16631, d22006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16631, d22006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16632 q = 1) (hb : d116750 q = 1) : d22007 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16632, d22007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16632, d22007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16633 q = 1) (hb : d116750 q = 1) : d22008 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16633, d22008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16633, d22008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16643 q = 1) (hb : d116750 q = 1) : d22018 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16643, d22018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16643, d22018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51701 (p : Pattern) (ha : d15042 p = 1) (hb : d116750 p = 1) : d22097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d116750 q = 1) : d22096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d116750 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15042 q = 1) (hb : d116750 q = 1) : d22097 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d22097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15042, d22097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51702 (p : Pattern) (ha : d16672 p = 1) (hb : d116750 p = 1) : d22069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15004 q = 1) (hb : d116750 q = 1) : d13164 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
  have h15 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15005 q = 1) (hb : d116750 q = 1) : d13165 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15006 q = 1) (hb : d116750 q = 1) : d13166 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15007 q = 1) (hb : d116750 q = 1) : d13167 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15008 q = 1) (hb : d116750 q = 1) : d22058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d22058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15008, d22058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d16672 q = 1) (hb : d116750 q = 1) : d22069 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d22069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16672, d22069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro51703 (p : Pattern) (ha : d16698 p = 1) (hb : d116750 p = 1) : d22103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d116750 q = 1) : d22098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d22098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
    | true =>
      simp only [d16693, d22098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51701 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d116750 q = 1) : d22099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d22099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d22099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d116750 q = 1) : d22100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d22100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d22100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d116750 q = 1) : d22101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d22101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d22101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d116750 q = 1) : d22102 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d22102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d22102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16698 q = 1) (hb : d116750 q = 1) : d22103 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16698, d22103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16698, d22103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51704 (p : Pattern) (ha : d16765 p = 1) (hb : d116750 p = 1) : d22197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16699 q = 1) (hb : d116750 q = 1) : d22104 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d22104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51703 q ha hb
    | true =>
      simp only [d16699, d22104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16700 q = 1) (hb : d116750 q = 1) : d22105 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d22105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d22105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16762 q = 1) (hb : d116750 q = 1) : d22194 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16762, d22194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16762, d22194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16763 q = 1) (hb : d116750 q = 1) : d22195 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16763, d22195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16763, d22195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16764 q = 1) (hb : d116750 q = 1) : d22196 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16764, d22196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16764, d22196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16765 q = 1) (hb : d116750 q = 1) : d22197 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16765, d22197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16765, d22197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51705 (p : Pattern) (ha : d16771 p = 1) (hb : d116750 p = 1) : d22203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16766 q = 1) (hb : d116750 q = 1) : d22198 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16766, d22198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51704 q ha hb
    | true =>
      simp only [d16766, d22198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16767 q = 1) (hb : d116750 q = 1) : d22199 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16767, d22199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16767, d22199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16768 q = 1) (hb : d116750 q = 1) : d22200 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16768, d22200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16768, d22200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16769 q = 1) (hb : d116750 q = 1) : d22201 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16769, d22201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16769, d22201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16770 q = 1) (hb : d116750 q = 1) : d22202 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16770, d22202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16770, d22202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16771 q = 1) (hb : d116750 q = 1) : d22203 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16771, d22203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16771, d22203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51706 (p : Pattern) (ha : d16491 p = 1) (hb : d116750 p = 1) : d21818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d116750 q = 1) : d21791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d116750 q = 1) : d21817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d21817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d21817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16491 q = 1) (hb : d116750 q = 1) : d21818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16491, d21818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16491, d21818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51707 (p : Pattern) (ha : d16493 p = 1) (hb : d116750 p = 1) : d21820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d116750 q = 1) : d21795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d116750 q = 1) : d21819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d21819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d21819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16493 q = 1) (hb : d116750 q = 1) : d21820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16493, d21820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16493, d21820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51708 (p : Pattern) (ha : d16500 p = 1) (hb : d116750 p = 1) : d21827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d116750 q = 1) : d21825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d21825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d21825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d116750 q = 1) : d21826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d21826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d21826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16500 q = 1) (hb : d116750 q = 1) : d21827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16500, d21827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16500, d21827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51709 (p : Pattern) (ha : d16503 p = 1) (hb : d116750 p = 1) : d21830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d116750 q = 1) : d21828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d21828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d21828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d116750 q = 1) : d21829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d21829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d21829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16503 q = 1) (hb : d116750 q = 1) : d21830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16503, d21830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16503, d21830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51710 (p : Pattern) (ha : d9752 p = 1) (hb : d116750 p = 1) : d21736 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1092 q = 1) : d1092 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9752 q = 1) (hb : d116750 q = 1) : d21736 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9752, d116750, d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d9752, d116750, d21736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51711 (p : Pattern) (ha : d16511 p = 1) (hb : d116750 p = 1) : d21846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d116750 q = 1) : d21837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d116750 q = 1) : d21838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9753 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
    | true =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9755 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16507 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16507, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16508 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16508, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16509 q = 1) (hb : d116750 q = 1) : d21839 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16509, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9763 q = 1) (hb : d116750 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36965 q ha hb
    | true =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9765 q = 1) (hb : d116750 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14836 q = 1) (hb : d116750 q = 1) : d21843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14836, d21843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14837 q = 1) (hb : d116750 q = 1) : d21844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14837, d21844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9778 q = 1) (hb : d116750 q = 1) : d21748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
    | true =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9780 q = 1) (hb : d116750 q = 1) : d21749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14758 q = 1) (hb : d116750 q = 1) : d21750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d21750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d21750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14759 q = 1) (hb : d116750 q = 1) : d21751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d21751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14759, d21751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16510 q = 1) (hb : d116750 q = 1) : d21845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, d21845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16510, d21845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16511 q = 1) (hb : d116750 q = 1) : d21846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, d21846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16511, d21846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51712 (p : Pattern) (ha : d16516 p = 1) (hb : d116750 p = 1) : d21856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d116750 q = 1) : d21851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
    | true =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9816 q = 1) (hb : d116750 q = 1) : d21852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13022 q = 1) (hb : d116750 q = 1) : d21853 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d21853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d21853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d116750 q = 1) : d21854 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, d21854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13023, d21854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14763 q = 1) (hb : d116750 q = 1) : d13027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d13027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14764 q = 1) (hb : d116750 q = 1) : d13028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14764, d13028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16515 q = 1) (hb : d116750 q = 1) : d21855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, d21855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16515, d21855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14765 q = 1) (hb : d116750 q = 1) : d21760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d21760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14765, d21760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16516 q = 1) (hb : d116750 q = 1) : d21856 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, d21856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16516, d21856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro51713 (p : Pattern) (ha : d16522 p = 1) (hb : d116750 p = 1) : d21862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d116750 q = 1) : d21847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d21847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51711 q ha hb
    | true =>
      simp only [d16512, d21847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d116750 q = 1) : d21848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d21848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d21848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d116750 q = 1) : d21849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d21849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d21849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d116750 q = 1) : d21857 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d21857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
    | true =>
      simp only [d16517, d21857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51712 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d116750 q = 1) : d21858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d21858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d21858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d116750 q = 1) : d21859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d21859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d21859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d116750 q = 1) : d21860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d21860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d21860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d116750 q = 1) : d21762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
    | true =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d116750 q = 1) : d21763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d116750 q = 1) : d21764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d116750 q = 1) : d21772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51683 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d116750 q = 1) : d21773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d116750 q = 1) : d21774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d116750 q = 1) : d21775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d116750 q = 1) : d21861 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d21861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d21861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16522 q = 1) (hb : d116750 q = 1) : d21862 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16522, d21862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16522, d21862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro51714 (p : Pattern) (ha : d16533 p = 1) (hb : d116750 p = 1) : d21873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d116750 q = 1) : d21863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d21863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51713 q ha hb
    | true =>
      simp only [d16523, d21863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d116750 q = 1) : d21864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d21864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d21864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d116750 q = 1) : d21868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51696 q ha hb
    | true =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d116750 q = 1) : d21869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d116750 q = 1) : d21870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d21870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d21870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d116750 q = 1) : d21871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d21871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d21871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d116750 q = 1) : d21872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d21872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d21872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16533 q = 1) (hb : d116750 q = 1) : d21873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16533, d21873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16533, d21873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51715 (p : Pattern) (ha : d12961 p = 1) (hb : d116750 p = 1) : d21948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d116750 q = 1) : d21776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d21776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d116750 q = 1) : d21948 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, d21948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51716 (p : Pattern) (ha : d16579 p = 1) (hb : d116750 p = 1) : d21954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d116750 q = 1) : d21762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51686 q ha hb
    | true =>
      simp only [d16444, d21762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d116750 q = 1) : d21763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d21763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d116750 q = 1) : d21764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d21764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d116750 q = 1) : d21772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16447, d21772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51683 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d116750 q = 1) : d21773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d21773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d116750 q = 1) : d21774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d21774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d116750 q = 1) : d21775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d21775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d116750 q = 1) : d21949 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d21949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51687 q ha hb
    | true =>
      simp only [d16574, d21949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51715 q ha hb
  have h9 (q : Pattern) (ha : d16575 q = 1) (hb : d116750 q = 1) : d21950 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d21950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d21950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16576 q = 1) (hb : d116750 q = 1) : d21951 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d21951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d21951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16577 q = 1) (hb : d116750 q = 1) : d21952 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d21952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16577, d21952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16578 q = 1) (hb : d116750 q = 1) : d21953 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d21953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d21953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16579 q = 1) (hb : d116750 q = 1) : d21954 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16579, d21954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16579, d21954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51717 (p : Pattern) (ha : d16585 p = 1) (hb : d116750 p = 1) : d21960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d116750 q = 1) : d21955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d21955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51716 q ha hb
    | true =>
      simp only [d16580, d21955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d116750 q = 1) : d21956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d21956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d21956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d116750 q = 1) : d21957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d21957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d21957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d116750 q = 1) : d21958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d21958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d21958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d116750 q = 1) : d21959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d21959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d21959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16585 q = 1) (hb : d116750 q = 1) : d21960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16585, d21960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16585, d21960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51718 (p : Pattern) (ha : d116750 p = 1) (hb : d128315 p = 1) : d150159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d116750 q = 1) : d21821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d21821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51706 q ha hb
    | true =>
      simp only [d16494, d21821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51707 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d116750 q = 1) : d21822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d21822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d21822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d116750 q = 1) : d21823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d21823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d21823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d116750 q = 1) : d21824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d21824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d21824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d116750 q = 1) : d21831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d21831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51708 q ha hb
    | true =>
      simp only [d16504, d21831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51709 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d116750 q = 1) : d21832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d21832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d21832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d116750 q = 1) : d21833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d21833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d21833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d116750 q = 1) : d21878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d21878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51714 q ha hb
    | true =>
      simp only [d16538, d21878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51697 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128311 q = 1) : d150155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128311, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d116750 q = 1) : d21961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d21961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51717 q ha hb
    | true =>
      simp only [d16586, d21961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d116750 q = 1) : d21962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d21962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d21962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128312 q = 1) : d150156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128313 q = 1) : d150157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128313, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128314 q = 1) : d150158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128314, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128315 q = 1) : d150159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128315, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128315, d150159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51719 (p : Pattern) (ha : d16592 p = 1) (hb : d116750 p = 1) : d21967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d116750 q = 1) : d21791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d21791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16490 q = 1) (hb : d116750 q = 1) : d21817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16490, d21817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16490, d21817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16592 q = 1) (hb : d116750 q = 1) : d21967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16592, d21967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16592, d21967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51720 (p : Pattern) (ha : d16593 p = 1) (hb : d116750 p = 1) : d21968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d116750 q = 1) : d21795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d21795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16492 q = 1) (hb : d116750 q = 1) : d21819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16492, d21819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16492, d21819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16593 q = 1) (hb : d116750 q = 1) : d21968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16593, d21968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16593, d21968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51721 (p : Pattern) (ha : d16598 p = 1) (hb : d116750 p = 1) : d21973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d116750 q = 1) : d21784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51688 q ha hb
    | true =>
      simp only [d16457, d21784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d116750 q = 1) : d21785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d21785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d116750 q = 1) : d21790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d21790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16498 q = 1) (hb : d116750 q = 1) : d21825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16498, d21825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16498, d21825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16499 q = 1) (hb : d116750 q = 1) : d21826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16499, d21826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16499, d21826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16598 q = 1) (hb : d116750 q = 1) : d21973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16598, d21973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16598, d21973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51722 (p : Pattern) (ha : d16599 p = 1) (hb : d116750 p = 1) : d21974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d116750 q = 1) : d21794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d21794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16501 q = 1) (hb : d116750 q = 1) : d21828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16501, d21828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16501, d21828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16502 q = 1) (hb : d116750 q = 1) : d21829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16502, d21829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16502, d21829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16599 q = 1) (hb : d116750 q = 1) : d21974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16599, d21974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16599, d21974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51723 (p : Pattern) (ha : d16603 p = 1) (hb : d116750 p = 1) : d21978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16523 q = 1) (hb : d116750 q = 1) : d21863 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16523, d21863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51713 q ha hb
    | true =>
      simp only [d16523, d21863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16524 q = 1) (hb : d116750 q = 1) : d21864 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16524, d21864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16524, d21864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16528 q = 1) (hb : d116750 q = 1) : d21868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51696 q ha hb
    | true =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16529 q = 1) (hb : d116750 q = 1) : d21869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16530 q = 1) (hb : d116750 q = 1) : d21870 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16530, d21870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16530, d21870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16531 q = 1) (hb : d116750 q = 1) : d21871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16531, d21871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16531, d21871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16532 q = 1) (hb : d116750 q = 1) : d21872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16532, d21872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16532, d21872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16603 q = 1) (hb : d116750 q = 1) : d21978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16603, d21978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16603, d21978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51724 (p : Pattern) (ha : d16604 p = 1) (hb : d116750 p = 1) : d21979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16528 q = 1) (hb : d116750 q = 1) : d21868 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51696 q ha hb
    | true =>
      simp only [d16528, d21868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16529 q = 1) (hb : d116750 q = 1) : d21869 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16529, d21869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d116750 q = 1) : d21788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51689 q ha hb
    | true =>
      simp only [d16461, d21788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d116750 q = 1) : d21789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d21789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16534 q = 1) (hb : d116750 q = 1) : d21874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16534, d21874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16534, d21874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16535 q = 1) (hb : d116750 q = 1) : d21875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16535, d21875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16535, d21875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16536 q = 1) (hb : d116750 q = 1) : d21876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16536, d21876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16536, d21876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16604 q = 1) (hb : d116750 q = 1) : d21979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16604, d21979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16604, d21979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51725 (p : Pattern) (ha : d16610 p = 1) (hb : d116750 p = 1) : d21985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16580 q = 1) (hb : d116750 q = 1) : d21955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16580, d21955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51716 q ha hb
    | true =>
      simp only [d16580, d21955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16581 q = 1) (hb : d116750 q = 1) : d21956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16581, d21956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16581, d21956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16582 q = 1) (hb : d116750 q = 1) : d21957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16582, d21957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16582, d21957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16583 q = 1) (hb : d116750 q = 1) : d21958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16583, d21958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16583, d21958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16584 q = 1) (hb : d116750 q = 1) : d21959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16584, d21959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16584, d21959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16610 q = 1) (hb : d116750 q = 1) : d21985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16610, d21985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16610, d21985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51726 (p : Pattern) (ha : d116750 p = 1) (hb : d128320 p = 1) : d150164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16494 q = 1) (hb : d116750 q = 1) : d21821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16494, d21821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51706 q ha hb
    | true =>
      simp only [d16494, d21821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51707 q ha hb
  have h2 (q : Pattern) (ha : d16495 q = 1) (hb : d116750 q = 1) : d21822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16495, d21822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16495, d21822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16496 q = 1) (hb : d116750 q = 1) : d21823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16496, d21823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16496, d21823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16497 q = 1) (hb : d116750 q = 1) : d21824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16497, d21824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16497, d21824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16504 q = 1) (hb : d116750 q = 1) : d21831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16504, d21831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51708 q ha hb
    | true =>
      simp only [d16504, d21831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51709 q ha hb
  have h6 (q : Pattern) (ha : d16505 q = 1) (hb : d116750 q = 1) : d21832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16505, d21832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16505, d21832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16506 q = 1) (hb : d116750 q = 1) : d21833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16506, d21833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16506, d21833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16538 q = 1) (hb : d116750 q = 1) : d21878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16538, d21878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51714 q ha hb
    | true =>
      simp only [d16538, d21878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51697 q ha hb
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128311 q = 1) : d150155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128311, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128311, d150155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d16586 q = 1) (hb : d116750 q = 1) : d21961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16586, d21961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51717 q ha hb
    | true =>
      simp only [d16586, d21961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16587 q = 1) (hb : d116750 q = 1) : d21962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16587, d21962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16587, d21962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116750 q = 1) (hb : d128312 q = 1) : d150156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128312, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128312, d150156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128313 q = 1) : d150157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128313, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128313, d150157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128314 q = 1) : d150158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128314, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128314, d150158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16594 q = 1) (hb : d116750 q = 1) : d21969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16594, d21969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51719 q ha hb
    | true =>
      simp only [d16594, d21969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51720 q ha hb
  have h16 (q : Pattern) (ha : d16595 q = 1) (hb : d116750 q = 1) : d21970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16595, d21970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16595, d21970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16596 q = 1) (hb : d116750 q = 1) : d21971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16596, d21971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16596, d21971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16597 q = 1) (hb : d116750 q = 1) : d21972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16597, d21972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16597, d21972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16600 q = 1) (hb : d116750 q = 1) : d21975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16600, d21975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51721 q ha hb
    | true =>
      simp only [d16600, d21975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51722 q ha hb
  have h20 (q : Pattern) (ha : d16601 q = 1) (hb : d116750 q = 1) : d21976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16601, d21976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16601, d21976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16602 q = 1) (hb : d116750 q = 1) : d21977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16602, d21977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16602, d21977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16605 q = 1) (hb : d116750 q = 1) : d21980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d21980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51723 q ha hb
    | true =>
      simp only [d16605, d21980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51724 q ha hb
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128316 q = 1) : d150160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d128316, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d16611 q = 1) (hb : d116750 q = 1) : d21986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d21986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51725 q ha hb
    | true =>
      simp only [d16611, d21986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16612 q = 1) (hb : d116750 q = 1) : d21987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d21987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16612, d21987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116750 q = 1) (hb : d128317 q = 1) : d150161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128317, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116750 q = 1) (hb : d128318 q = 1) : d150162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128318, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d128318, d150162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116750 q = 1) (hb : d128319 q = 1) : d150163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128319, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d128319, d150163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116750 q = 1) (hb : d128320 q = 1) : d150164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128320, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128320, d150164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro51727 (p : Pattern) (ha : d116750 p = 1) (hb : d128327 p = 1) : d150171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16605 q = 1) (hb : d116750 q = 1) : d21980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16605, d21980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51723 q ha hb
    | true =>
      simp only [d16605, d21980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51724 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128316 q = 1) : d150160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128316, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128316, d150160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16611 q = 1) (hb : d116750 q = 1) : d21986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16611, d21986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51725 q ha hb
    | true =>
      simp only [d16611, d21986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16612 q = 1) (hb : d116750 q = 1) : d21987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16612, d21987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16612, d21987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128317 q = 1) : d150161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128317, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128317, d150161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128325 q = 1) : d150169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128325, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128325, d150169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128326 q = 1) : d150170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128326, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128326, d150170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128327 q = 1) : d150171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d150171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128327, d150171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51728 (p : Pattern) (ha : d15024 p = 1) (hb : d116750 p = 1) : d22078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d116750 q = 1) : d22073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d22073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d22073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
  have h2 (q : Pattern) (ha : d5018 q = 1) (hb : d116750 q = 1) : d21766 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29466 q ha hb
    | true =>
      simp only [d5018, d21766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6351 q = 1) (hb : d116750 q = 1) : d22074 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d22074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6351, d22074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5019 q = 1) (hb : d116750 q = 1) : d21767 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5019, d21767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6352 q = 1) (hb : d116750 q = 1) : d22075 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d22075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6352, d22075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6353 q = 1) (hb : d116750 q = 1) : d22076 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d22076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6353, d22076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6354 q = 1) (hb : d116750 q = 1) : d22077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d22077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6354, d22077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d116750 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15024 q = 1) (hb : d116750 q = 1) : d22078 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d22078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15024, d22078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro51729 (p : Pattern) (ha : d16655 p = 1) (hb : d116750 p = 1) : d22042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d116750 q = 1) : d22024 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d116750 q = 1) : d22025 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d116750 q = 1) : d22026 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d116750 q = 1) : d22027 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16649 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
  have h8 (q : Pattern) (ha : d9753 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51710 q ha hb
    | true =>
      simp only [d9753, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16650 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16650, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9755 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9755, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16651 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16651, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16652 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16652, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16653 q = 1) (hb : d116750 q = 1) : d22032 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16653, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14987 q = 1) (hb : d116750 q = 1) : d22033 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d22033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36965 q ha hb
  have h15 (q : Pattern) (ha : d9763 q = 1) (hb : d116750 q = 1) : d21841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36965 q ha hb
    | true =>
      simp only [d9763, d21841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14988 q = 1) (hb : d116750 q = 1) : d22034 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14988, d22034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9765 q = 1) (hb : d116750 q = 1) : d21842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9765, d21842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14989 q = 1) (hb : d116750 q = 1) : d22035 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14989, d22035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14990 q = 1) (hb : d116750 q = 1) : d22036 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14990, d22036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d14994 q = 1) (hb : d116750 q = 1) : d22037 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d22037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d22037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
  have h21 (q : Pattern) (ha : d9778 q = 1) (hb : d116750 q = 1) : d21748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
    | true =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14995 q = 1) (hb : d116750 q = 1) : d22038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d22038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14995, d22038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9780 q = 1) (hb : d116750 q = 1) : d21749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14996 q = 1) (hb : d116750 q = 1) : d22039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d22039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d14996, d22039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14997 q = 1) (hb : d116750 q = 1) : d22040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d22040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14997, d22040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16654 q = 1) (hb : d116750 q = 1) : d22041 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d22041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16654, d22041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16655 q = 1) (hb : d116750 q = 1) : d22042 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d22042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16655, d22042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro51730 (p : Pattern) (ha : d16662 p = 1) (hb : d116750 p = 1) : d22049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16656 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
  have h8 (q : Pattern) (ha : d9789 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51685 q ha hb
    | true =>
      simp only [d9789, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16657 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16657, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9791 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9791, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16658 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16658, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16659 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16659, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16660 q = 1) (hb : d116750 q = 1) : d22047 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16660, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14994 q = 1) (hb : d116750 q = 1) : d22037 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d22037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d22037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
  have h15 (q : Pattern) (ha : d9778 q = 1) (hb : d116750 q = 1) : d21748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36937 q ha hb
    | true =>
      simp only [d9778, d21748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14995 q = 1) (hb : d116750 q = 1) : d22038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d22038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14995, d22038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9780 q = 1) (hb : d116750 q = 1) : d21749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9780, d21749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14996 q = 1) (hb : d116750 q = 1) : d22039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d22039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14996, d22039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14997 q = 1) (hb : d116750 q = 1) : d22040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d22040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14997, d22040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15004 q = 1) (hb : d116750 q = 1) : d13164 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
  have h21 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15005 q = 1) (hb : d116750 q = 1) : d13165 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15006 q = 1) (hb : d116750 q = 1) : d13166 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d15007 q = 1) (hb : d116750 q = 1) : d13167 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16661 q = 1) (hb : d116750 q = 1) : d22048 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d22048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16661, d22048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16662 q = 1) (hb : d116750 q = 1) : d22049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d22049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16662, d22049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro51731 (p : Pattern) (ha : d16667 p = 1) (hb : d116750 p = 1) : d22059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d116750 q = 1) : d22053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d22053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d22053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
  have h2 (q : Pattern) (ha : d9814 q = 1) (hb : d116750 q = 1) : d21851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29493 q ha hb
    | true =>
      simp only [d9814, d21851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13161 q = 1) (hb : d116750 q = 1) : d22054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d22054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13161, d22054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9816 q = 1) (hb : d116750 q = 1) : d21852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9816, d21852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13162 q = 1) (hb : d116750 q = 1) : d22055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d22055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13162, d22055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13163 q = 1) (hb : d116750 q = 1) : d22056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d22056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13163, d22056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15004 q = 1) (hb : d116750 q = 1) : d13164 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d13164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
  have h8 (q : Pattern) (ha : d9800 q = 1) (hb : d116750 q = 1) : d13025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36939 q ha hb
    | true =>
      simp only [d9800, d13025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15005 q = 1) (hb : d116750 q = 1) : d13165 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15005, d13165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9802 q = 1) (hb : d116750 q = 1) : d13026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9802, d13026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15006 q = 1) (hb : d116750 q = 1) : d13166 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15006, d13166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15007 q = 1) (hb : d116750 q = 1) : d13167 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15007, d13167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16666 q = 1) (hb : d116750 q = 1) : d22057 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d22057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16666, d22057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15008 q = 1) (hb : d116750 q = 1) : d22058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d22058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15008, d22058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16667 q = 1) (hb : d116750 q = 1) : d22059 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d22059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16667, d22059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51732 (p : Pattern) (ha : d16681 p = 1) (hb : d116750 p = 1) : d22084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d116750 q = 1) : d22050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d22050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51729 q ha hb
    | true =>
      simp only [d16663, d22050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51730 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d116750 q = 1) : d22051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d22051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d22051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d116750 q = 1) : d22052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d22052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d22052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d116750 q = 1) : d22060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d22060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51730 q ha hb
    | true =>
      simp only [d16668, d22060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51731 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d116750 q = 1) : d22061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d22061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d22061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d116750 q = 1) : d22062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d22062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d22062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d116750 q = 1) : d22063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d22063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d22063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d116750 q = 1) : d22070 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51730 q ha hb
    | true =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d116750 q = 1) : d22071 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d116750 q = 1) : d22072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d116750 q = 1) : d22079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
    | true =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51728 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d116750 q = 1) : d22080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d116750 q = 1) : d22081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d116750 q = 1) : d22082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d116750 q = 1) : d22083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d22083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d22083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16681 q = 1) (hb : d116750 q = 1) : d22084 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16681, d22084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16681, d22084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro51733 (p : Pattern) (ha : d16686 p = 1) (hb : d116750 p = 1) : d22089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d116750 q = 1) : d22070 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51730 q ha hb
    | true =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d116750 q = 1) : d22071 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d116750 q = 1) : d22072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d116750 q = 1) : d22079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
    | true =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51728 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d116750 q = 1) : d22080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d116750 q = 1) : d22081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d116750 q = 1) : d22082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d116750 q = 1) : d22087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d22087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d22087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d116750 q = 1) : d22088 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d22088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d22088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16686 q = 1) (hb : d116750 q = 1) : d22089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16686, d22089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16686, d22089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro51734 (p : Pattern) (ha : d16692 p = 1) (hb : d116750 p = 1) : d22095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16682 q = 1) (hb : d116750 q = 1) : d22085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16682, d22085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51732 q ha hb
    | true =>
      simp only [d16682, d22085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16683 q = 1) (hb : d116750 q = 1) : d22086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16683, d22086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16683, d22086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16687 q = 1) (hb : d116750 q = 1) : d22090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d22090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51733 q ha hb
    | true =>
      simp only [d16687, d22090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16688 q = 1) (hb : d116750 q = 1) : d22091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d22091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d22091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16689 q = 1) (hb : d116750 q = 1) : d22092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16689, d22092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16689, d22092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16690 q = 1) (hb : d116750 q = 1) : d22093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16690, d22093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16690, d22093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16691 q = 1) (hb : d116750 q = 1) : d22094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16691, d22094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16691, d22094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16692 q = 1) (hb : d116750 q = 1) : d22095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16692, d22095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16692, d22095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51735 (p : Pattern) (ha : d16704 p = 1) (hb : d116750 p = 1) : d22109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16687 q = 1) (hb : d116750 q = 1) : d22090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16687, d22090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51733 q ha hb
    | true =>
      simp only [d16687, d22090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16688 q = 1) (hb : d116750 q = 1) : d22091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16688, d22091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16688, d22091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d116750 q = 1) : d22104 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d22104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51703 q ha hb
    | true =>
      simp only [d16699, d22104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d116750 q = 1) : d22105 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d22105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d22105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16701 q = 1) (hb : d116750 q = 1) : d22106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16701, d22106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16701, d22106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16702 q = 1) (hb : d116750 q = 1) : d22107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16702, d22107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16702, d22107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16703 q = 1) (hb : d116750 q = 1) : d22108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16703, d22108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16703, d22108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16704 q = 1) (hb : d116750 q = 1) : d22109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16704, d22109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16704, d22109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51736 (p : Pattern) (ha : d13190 p = 1) (hb : d116750 p = 1) : d22174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d116750 q = 1) : d22096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d22096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13190 q = 1) (hb : d116750 q = 1) : d22174 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, d22174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro51737 (p : Pattern) (ha : d16748 p = 1) (hb : d116750 p = 1) : d22180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d116750 q = 1) : d22070 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51730 q ha hb
    | true =>
      simp only [d16673, d22070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d116750 q = 1) : d22071 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d22071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d116750 q = 1) : d22072 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d22072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d116750 q = 1) : d22079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
    | true =>
      simp only [d16676, d22079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51728 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d116750 q = 1) : d22080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d22080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d116750 q = 1) : d22081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d22081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d116750 q = 1) : d22082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d22082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d116750 q = 1) : d22175 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d22175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51702 q ha hb
    | true =>
      simp only [d16743, d22175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51736 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d116750 q = 1) : d22176 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d22176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d22176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d116750 q = 1) : d22177 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d22177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d22177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d116750 q = 1) : d22178 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d22178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d22178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d116750 q = 1) : d22179 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d22179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d22179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16748 q = 1) (hb : d116750 q = 1) : d22180 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16748, d22180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16748, d22180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51738 (p : Pattern) (ha : d16754 p = 1) (hb : d116750 p = 1) : d22186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16749 q = 1) (hb : d116750 q = 1) : d22181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16749, d22181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51737 q ha hb
    | true =>
      simp only [d16749, d22181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16750 q = 1) (hb : d116750 q = 1) : d22182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16750, d22182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16750, d22182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16751 q = 1) (hb : d116750 q = 1) : d22183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16751, d22183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16751, d22183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16752 q = 1) (hb : d116750 q = 1) : d22184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16752, d22184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16752, d22184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16753 q = 1) (hb : d116750 q = 1) : d22185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16753, d22185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16753, d22185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16754 q = 1) (hb : d116750 q = 1) : d22186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16754, d22186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16754, d22186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro51739 (p : Pattern) (ha : d116750 p = 1) (hb : d128337 p = 1) : d150181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16705 q = 1) (hb : d116750 q = 1) : d22110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16705, d22110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51734 q ha hb
    | true =>
      simp only [d16705, d22110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51735 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128333 q = 1) : d150177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d150177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d150177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d16755 q = 1) (hb : d116750 q = 1) : d22187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16755, d22187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51738 q ha hb
    | true =>
      simp only [d16755, d22187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16756 q = 1) (hb : d116750 q = 1) : d22188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16756, d22188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16756, d22188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128334 q = 1) : d150178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d150178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128334, d150178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128335 q = 1) : d150179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d150179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128335, d150179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116750 q = 1) (hb : d128336 q = 1) : d150180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d150180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128336, d150180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128337 q = 1) : d150181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d150181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128337, d150181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro51740 (p : Pattern) (ha : d116750 p = 1) (hb : d128343 p = 1) : d150187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16477 q = 1) (hb : d116750 q = 1) : d21804 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16477, d21804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16477, d21804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51692 q ha hb
  have h2 (q : Pattern) (ha : d16478 q = 1) (hb : d116750 q = 1) : d21805 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16478, d21805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16478, d21805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16487 q = 1) (hb : d116750 q = 1) : d21814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d21814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51692 q ha hb
    | true =>
      simp only [d16487, d21814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51695 q ha hb
  have h4 (q : Pattern) (ha : d16488 q = 1) (hb : d116750 q = 1) : d21815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d21815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16488, d21815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16489 q = 1) (hb : d116750 q = 1) : d21816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16489, d21816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16489, d21816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128321 q = 1) : d150165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128321, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51718 q ha hb
    | true =>
      simp only [d128321, d150165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51726 q ha hb
  have h7 (q : Pattern) (ha : d16635 q = 1) (hb : d116750 q = 1) : d22010 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16635, d22010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51698 q ha hb
    | true =>
      simp only [d16635, d22010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51699 q ha hb
  have h8 (q : Pattern) (ha : d116750 q = 1) (hb : d128322 q = 1) : d150166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128322, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128322, d150166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116750 q = 1) (hb : d128323 q = 1) : d150167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d150167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128323, d150167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116750 q = 1) (hb : d128324 q = 1) : d150168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d150168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128324, d150168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116750 q = 1) (hb : d128328 q = 1) : d150172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d150172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128328, d150172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51727 q ha hb
  have h12 (q : Pattern) (ha : d16644 q = 1) (hb : d116750 q = 1) : d22019 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16644, d22019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16644, d22019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51700 q ha hb
  have h13 (q : Pattern) (ha : d116750 q = 1) (hb : d128329 q = 1) : d150173 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d150173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128329, d150173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116750 q = 1) (hb : d128330 q = 1) : d150174 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d150174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128330, d150174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116750 q = 1) (hb : d128331 q = 1) : d150175 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d150175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128331, d150175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116750 q = 1) (hb : d128332 q = 1) : d150176 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d150176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128332, d150176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116750 q = 1) (hb : d128338 q = 1) : d150182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d150182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128338, d150182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51739 q ha hb
  have h18 (q : Pattern) (ha : d16772 q = 1) (hb : d116750 q = 1) : d22204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16772, d22204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16772, d22204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51705 q ha hb
  have h19 (q : Pattern) (ha : d116750 q = 1) (hb : d128339 q = 1) : d150183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d150183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128339, d150183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116750 q = 1) (hb : d128340 q = 1) : d150184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d150184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128340, d150184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116750 q = 1) (hb : d128341 q = 1) : d150185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d150185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128341, d150185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116750 q = 1) (hb : d128342 q = 1) : d150186 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d150186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128342, d150186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116750 q = 1) (hb : d128343 q = 1) : d150187 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d150187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128343, d150187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro51741 (p : Pattern) (ha : d116750 p = 1) (hb : d128349 p = 1) : d150193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116750 q = 1) (hb : d128344 q = 1) : d150188 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d150188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128344, d150188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51740 q ha hb
  have h2 (q : Pattern) (ha : d116750 q = 1) (hb : d128345 q = 1) : d150189 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d150189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128345, d150189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d116750 q = 1) (hb : d128346 q = 1) : d150190 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d150190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128346, d150190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d116750 q = 1) (hb : d128347 q = 1) : d150191 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d150191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128347, d150191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116750 q = 1) (hb : d128348 q = 1) : d150192 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d150192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128348, d150192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116750 q = 1) (hb : d128349 q = 1) : d150193 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d150193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128349, d150193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro51742 (p : Pattern) (ha : d15166 p = 1) (hb : d116750 p = 1) : d22249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d116750 q = 1) : d22244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29522 q ha hb
    | true =>
      simp only [d5134, d22244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d116750 q = 1) : d22245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d22245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d116750 q = 1) : d22246 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d22246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d22246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d116750 q = 1) : d22247 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d22247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d22247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d116750 q = 1) : d22248 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15165 q = 1) (hb : d116750 q = 1) : d15165 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15166 q = 1) (hb : d116750 q = 1) : d22249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d22249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15166, d22249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51743 (p : Pattern) (ha : d15171 p = 1) (hb : d116750 p = 1) : d22255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d116750 q = 1) : d22254 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15165 q = 1) (hb : d116750 q = 1) : d15165 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15171 q = 1) (hb : d116750 q = 1) : d22255 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d22255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15171, d22255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro51744 (p : Pattern) (ha : d10073 p = 1) (hb : d116750 p = 1) : d22219 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1553 q = 1) : d1553 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10073 q = 1) (hb : d116750 q = 1) : d22219 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10073, d116750, d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10073, d116750, d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51745 (p : Pattern) (ha : d16791 p = 1) (hb : d116750 p = 1) : d22231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10074 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51744 q ha hb
    | true =>
      simp only [d10074, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10076, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16787 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16787, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16788 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16788, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16789 q = 1) (hb : d116750 q = 1) : d22224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16789, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10063 q = 1) (hb : d116750 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36997 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d116750 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15151 q = 1) (hb : d116750 q = 1) : d22228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d22228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15152 q = 1) (hb : d116750 q = 1) : d22229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15152, d22229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15156 q = 1) (hb : d116750 q = 1) : d13353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15157 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16790 q = 1) (hb : d116750 q = 1) : d22230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d22230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16790, d22230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16791 q = 1) (hb : d116750 q = 1) : d22231 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d22231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16791, d22231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro51746 (p : Pattern) (ha : d10114 p = 1) (hb : d116750 p = 1) : d22232 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1568 q = 1) : d1568 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10114 q = 1) (hb : d116750 q = 1) : d22232 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10114, d116750, d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10114, d116750, d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro51747 (p : Pattern) (ha : d16795 p = 1) (hb : d116750 p = 1) : d22239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10115 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51746 q ha hb
    | true =>
      simp only [d10115, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10117, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16792 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16792, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16793 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16793, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16794 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16794, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15156 q = 1) (hb : d116750 q = 1) : d13353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15157 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15158 q = 1) (hb : d116750 q = 1) : d22238 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15158, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16795 q = 1) (hb : d116750 q = 1) : d22239 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d22239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16795, d22239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro51748 (p : Pattern) (ha : d16808 p = 1) (hb : d116750 p = 1) : d22261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d116750 q = 1) : d22240 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d22240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51745 q ha hb
    | true =>
      simp only [d16796, d22240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51747 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d116750 q = 1) : d22241 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d22241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d22241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d116750 q = 1) : d22242 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d22242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d22242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d116750 q = 1) : d22250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d22250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51747 q ha hb
    | true =>
      simp only [d16799, d22250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51742 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d116750 q = 1) : d22251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d22251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d22251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d116750 q = 1) : d22252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d22252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d22252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d116750 q = 1) : d22253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d22253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d22253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d116750 q = 1) : d22256 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d22256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51747 q ha hb
    | true =>
      simp only [d16803, d22256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51743 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d116750 q = 1) : d22257 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d22257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d22257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d116750 q = 1) : d22258 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d22258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d22258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d116750 q = 1) : d22259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d22259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d22259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d116750 q = 1) : d22260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d22260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d22260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d116750 q = 1) : d22261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d22261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d22261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro51749 (p : Pattern) (ha : d16812 p = 1) (hb : d116750 p = 1) : d22265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d116750 q = 1) : d22256 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d22256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51747 q ha hb
    | true =>
      simp only [d16803, d22256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51743 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d116750 q = 1) : d22257 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d22257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d22257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d116750 q = 1) : d22258 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d22258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d22258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d116750 q = 1) : d22259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d22259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d22259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d116750 q = 1) : d22264 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d22264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d22264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d116750 q = 1) : d22265 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d22265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d22265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
