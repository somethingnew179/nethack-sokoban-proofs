import NetHack.Soko22Hazard87.EqIntroBlocks0046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro11750 (p : Pattern) (selected : d136278 p = 0) : d137555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136273 q = 0) : d137550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136273, d137550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11749 q selected
    | true =>
      simp only [d136273, d137550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136274 q = 0) : d137551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136274, d137551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136274, d137551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136275 q = 0) : d137552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136275, d137552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136275, d137552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136276 q = 0) : d137553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136276, d137553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136276, d137553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136277 q = 0) : d137554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136277, d137554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136277, d137554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136278 q = 0) : d137555 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136278, d137555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136278, d137555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11751 (p : Pattern) (selected : d136284 p = 0) : d137561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136063 q = 0) : d137388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136063, d137388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136063, d137388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11705 q selected
  have h2 (q : Pattern) (selected : d136064 q = 0) : d137389 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136064, d137389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136064, d137389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136073 q = 0) : d137398 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136073, d137398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11705 q selected
    | true =>
      simp only [d136073, d137398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11708 q selected
  have h4 (q : Pattern) (selected : d136074 q = 0) : d137399 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136074, d137399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136074, d137399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136075 q = 0) : d137400 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136075, d137400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136075, d137400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136170 q = 0) : d137469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136170, d137469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11722 q selected
    | true =>
      simp only [d136170, d137469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11731 q selected
  have h7 (q : Pattern) (selected : d136183 q = 0) : d137482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136183, d137482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11732 q selected
    | true =>
      simp only [d136183, d137482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11733 q selected
  have h8 (q : Pattern) (selected : d136184 q = 0) : d137483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136184, d137483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136184, d137483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136185 q = 0) : d137484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136185, d137484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136185, d137484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d136186 q = 0) : d137485 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136186, d137485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136186, d137485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136190 q = 0) : d137489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136190, d137489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136190, d137489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11734 q selected
  have h12 (q : Pattern) (selected : d136192 q = 0) : d137491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136192, d137491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136192, d137491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11735 q selected
  have h13 (q : Pattern) (selected : d136193 q = 0) : d137492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136193, d137492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136193, d137492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136194 q = 0) : d137493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136194, d137493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136194, d137493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d136195 q = 0) : d137494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136195, d137494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d136195, d137494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d136196 q = 0) : d137495 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136196, d137495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136196, d137495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136268 q = 0) : d137549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136268, d137549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136268, d137549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11748 q selected
  have h18 (q : Pattern) (selected : d136279 q = 0) : d137556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136279, d137556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136279, d137556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11750 q selected
  have h19 (q : Pattern) (selected : d136280 q = 0) : d137557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136280, d137557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136280, d137557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136281 q = 0) : d137558 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136281, d137558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136281, d137558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d136282 q = 0) : d137559 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136282, d137559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d136282, d137559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d136283 q = 0) : d137560 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136283, d137560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136283, d137560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136284 q = 0) : d137561 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136284, d137561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136284, d137561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11752 (p : Pattern) (selected : d136290 p = 0) : d137567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136285 q = 0) : d137562 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136285, d137562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136285, d137562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11751 q selected
  have h2 (q : Pattern) (selected : d136286 q = 0) : d137563 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136286, d137563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136286, d137563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136287 q = 0) : d137564 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136287, d137564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136287, d137564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136288 q = 0) : d137565 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136288, d137565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136288, d137565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136289 q = 0) : d137566 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136289, d137566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136289, d137566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136290 q = 0) : d137567 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136290, d137567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136290, d137567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11753 (p : Pattern) (selected : d136301 p = 0) : d137578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h2 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136296 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6206 q selected
  have h4 (q : Pattern) (selected : d136297 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136298 q = 0) : d137575 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136299 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136300 q = 0) : d137577 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136300, d137577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136300, d137577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136301 q = 0) : d137578 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136301, d137578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136301, d137578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11754 (p : Pattern) (selected : d136305 p = 0) : d137582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136296 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6206 q selected
  have h2 (q : Pattern) (selected : d136297 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136299 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136299, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136304 q = 0) : d137581 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136304, d137581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136304, d137581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136305 q = 0) : d137582 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136305, d137582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136305, d137582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11755 (p : Pattern) (selected : d136311 p = 0) : d137588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136309 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136310 q = 0) : d137587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136310, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136310, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136311 q = 0) : d137588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136311, d137588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136311, d137588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11756 (p : Pattern) (selected : d136315 p = 0) : d137592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136313 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136314 q = 0) : d137591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136314, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136314, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136315 q = 0) : d137592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136315, d137592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136315, d137592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11757 (p : Pattern) (selected : d136321 p = 0) : d137598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136316 q = 0) : d137593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11755 q selected
    | true =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d136317 q = 0) : d137594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136318 q = 0) : d137595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136319 q = 0) : d137596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136320 q = 0) : d137597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136321 q = 0) : d137598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136321, d137598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136321, d137598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11758 (p : Pattern) (selected : d136324 p = 0) : d137601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136309 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136310 q = 0) : d137587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136310, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136310, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136324 q = 0) : d137601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136324, d137601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136324, d137601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11759 (p : Pattern) (selected : d136325 p = 0) : d137602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136313 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136314 q = 0) : d137591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136314, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136314, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136325 q = 0) : d137602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136325, d137602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136325, d137602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11760 (p : Pattern) (selected : d136331 p = 0) : d137608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136316 q = 0) : d137593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11755 q selected
    | true =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d136317 q = 0) : d137594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136318 q = 0) : d137595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136319 q = 0) : d137596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136320 q = 0) : d137597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136326 q = 0) : d137603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136326, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11758 q selected
    | true =>
      simp only [d136326, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11759 q selected
  have h7 (q : Pattern) (selected : d136327 q = 0) : d137604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136327, d137604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136327, d137604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136328 q = 0) : d137605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136328, d137605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136328, d137605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136329 q = 0) : d137606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136329, d137606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136329, d137606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136330 q = 0) : d137607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136330, d137607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136330, d137607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136331 q = 0) : d137608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136331, d137608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136331, d137608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11761 (p : Pattern) (selected : d136336 p = 0) : d137613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136309 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136335 q = 0) : d137612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136335, d137612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136335, d137612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136336 q = 0) : d137613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136336, d137613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136336, d137613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11762 (p : Pattern) (selected : d136338 p = 0) : d137615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136313 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136337 q = 0) : d137614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136337, d137614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136337, d137614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136338 q = 0) : d137615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136338, d137615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136338, d137615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11763 (p : Pattern) (selected : d136345 p = 0) : d137622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136343 q = 0) : d137620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136343, d137620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136343, d137620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136344 q = 0) : d137621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136344, d137621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136344, d137621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136345 q = 0) : d137622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136345, d137622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136345, d137622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11764 (p : Pattern) (selected : d136348 p = 0) : d137625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136346 q = 0) : d137623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136346, d137623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136346, d137623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136347 q = 0) : d137624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136347, d137624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136347, d137624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136348 q = 0) : d137625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136348, d137625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136348, d137625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11765 (p : Pattern) (selected : d136356 p = 0) : d137633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136352 q = 0) : d137629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136352, d137629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136352, d137629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6220 q selected
  have h2 (q : Pattern) (selected : d136353 q = 0) : d137630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136353, d137630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136353, d137630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h4 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136354 q = 0) : d137631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136354, d137631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136354, d137631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136296 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6206 q selected
  have h7 (q : Pattern) (selected : d136297 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136298 q = 0) : d137575 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136355 q = 0) : d137632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136355, d137632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136355, d137632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136356 q = 0) : d137633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136356, d137633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136356, d137633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11766 (p : Pattern) (selected : d136362 p = 0) : d137639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136357 q = 0) : d137634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136357, d137634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11765 q selected
    | true =>
      simp only [d136357, d137634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136358 q = 0) : d137635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136358, d137635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136358, d137635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136359 q = 0) : d137636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136359, d137636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136359, d137636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136360 q = 0) : d137637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136360, d137637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136360, d137637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136361 q = 0) : d137638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136361, d137638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136361, d137638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136362 q = 0) : d137639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136362, d137639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136362, d137639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11767 (p : Pattern) (selected : d136371 p = 0) : d137578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136364 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136364, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136364, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6225 q selected
  have h2 (q : Pattern) (selected : d136365 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136365, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136365, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136366 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6226 q selected
  have h4 (q : Pattern) (selected : d136367 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136368 q = 0) : d137575 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136368, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136368, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136369 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136370 q = 0) : d137577 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136370, d137577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136370, d137577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136371 q = 0) : d137578 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136371, d137578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136371, d137578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11768 (p : Pattern) (selected : d136375 p = 0) : d137582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136366 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6226 q selected
  have h2 (q : Pattern) (selected : d136367 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136369 q = 0) : d137576 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136369, d137576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136374 q = 0) : d137581 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136374, d137581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136374, d137581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136375 q = 0) : d137582 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136375, d137582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136375, d137582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11769 (p : Pattern) (selected : d136381 p = 0) : d137588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136372 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136372, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11767 q selected
    | true =>
      simp only [d136372, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136373 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136373, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136373, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136378 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136378, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136378, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136379 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136379, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136379, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136380 q = 0) : d137587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136380, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136380, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136381 q = 0) : d137588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136381, d137588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136381, d137588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11770 (p : Pattern) (selected : d136385 p = 0) : d137592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136382 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136382, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136382, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136383 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136383, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136383, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136384 q = 0) : d137591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136384, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136384, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136385 q = 0) : d137592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136385, d137592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136385, d137592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11771 (p : Pattern) (selected : d5634 p = 0) : d74360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5630 q = 0) : d74356 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3386 q selected
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5631 q = 0) : d74357 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5632 q = 0) : d74358 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5633 q = 0) : d74359 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5634 q = 0) : d74360 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11772 (p : Pattern) (selected : d136392 p = 0) : d137646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136294 q = 0) : d137571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136294, d137571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
  have h2 (q : Pattern) (selected : d136295 q = 0) : d137572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136295, d137572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136296 q = 0) : d137573 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136296, d137573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6206 q selected
  have h4 (q : Pattern) (selected : d136297 q = 0) : d137574 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136297, d137574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136298 q = 0) : d137575 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136298, d137575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136388 q = 0) : d137642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136388, d137642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136388, d137642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11771 q selected
  have h7 (q : Pattern) (selected : d136389 q = 0) : d137643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136389, d137643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136389, d137643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136390 q = 0) : d137644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136390, d137644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136390, d137644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136391 q = 0) : d137645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136391, d137645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136391, d137645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136392 q = 0) : d137646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136392, d137646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136392, d137646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11773 (p : Pattern) (selected : d136398 p = 0) : d137652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136393 q = 0) : d137647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136393, d137647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11772 q selected
    | true =>
      simp only [d136393, d137647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136394 q = 0) : d137648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136394, d137648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136394, d137648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136395 q = 0) : d137649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136395, d137649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136395, d137649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136396 q = 0) : d137650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136396, d137650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136396, d137650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136397 q = 0) : d137651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136397, d137651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136397, d137651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136398 q = 0) : d137652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136398, d137652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136398, d137652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11774 (p : Pattern) (selected : d136404 p = 0) : d137658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136339 q = 0) : d137616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136339, d137616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11761 q selected
    | true =>
      simp only [d136339, d137616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11762 q selected
  have h2 (q : Pattern) (selected : d136340 q = 0) : d137617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136340, d137617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136340, d137617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136341 q = 0) : d137618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136341, d137618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136341, d137618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136342 q = 0) : d137619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136342, d137619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136342, d137619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136349 q = 0) : d137626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136349, d137626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11763 q selected
    | true =>
      simp only [d136349, d137626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11764 q selected
  have h6 (q : Pattern) (selected : d136350 q = 0) : d137627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136350, d137627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136350, d137627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136351 q = 0) : d137628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136351, d137628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136351, d137628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136363 q = 0) : d137640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136363, d137640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11766 q selected
    | true =>
      simp only [d136363, d137640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11755 q selected
  have h9 (q : Pattern) (selected : d136386 q = 0) : d137593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136386, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11769 q selected
    | true =>
      simp only [d136386, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11770 q selected
  have h10 (q : Pattern) (selected : d136387 q = 0) : d137641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136387, d137641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136387, d137641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136399 q = 0) : d137653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136399, d137653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11773 q selected
    | true =>
      simp only [d136399, d137653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136400 q = 0) : d137654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136400, d137654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136400, d137654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136401 q = 0) : d137655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136401, d137655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136401, d137655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136402 q = 0) : d137656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136402, d137656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136402, d137656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136403 q = 0) : d137657 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136403, d137657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136403, d137657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136404 q = 0) : d137658 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136404, d137658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136404, d137658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11775 (p : Pattern) (selected : d136405 p = 0) : d137659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136309 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136309, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136335 q = 0) : d137612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136335, d137612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136335, d137612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136405 q = 0) : d137659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136405, d137659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136405, d137659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11776 (p : Pattern) (selected : d136406 p = 0) : d137660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136313 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136313, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136337 q = 0) : d137614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136337, d137614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136337, d137614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136406 q = 0) : d137660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136406, d137660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136406, d137660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11777 (p : Pattern) (selected : d136411 p = 0) : d137665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136308 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136308, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136343 q = 0) : d137620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136343, d137620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136343, d137620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136344 q = 0) : d137621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136344, d137621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136344, d137621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136411 q = 0) : d137665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136411, d137665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136411, d137665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11778 (p : Pattern) (selected : d136412 p = 0) : d137666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136306 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11754 q selected
    | true =>
      simp only [d136306, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136307 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136307, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136312 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136312, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136346 q = 0) : d137623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136346, d137623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136346, d137623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136347 q = 0) : d137624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136347, d137624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136347, d137624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136412 q = 0) : d137666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136412, d137666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136412, d137666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11779 (p : Pattern) (selected : d136416 p = 0) : d137670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136357 q = 0) : d137634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136357, d137634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11765 q selected
    | true =>
      simp only [d136357, d137634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136358 q = 0) : d137635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136358, d137635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136358, d137635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136302 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11753 q selected
    | true =>
      simp only [d136302, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136303 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136303, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136359 q = 0) : d137636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136359, d137636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136359, d137636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136360 q = 0) : d137637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136360, d137637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136360, d137637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136361 q = 0) : d137638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136361, d137638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136361, d137638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136416 q = 0) : d137670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136416, d137670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136416, d137670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11780 (p : Pattern) (selected : d136418 p = 0) : d137601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136372 q = 0) : d137579 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136372, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11767 q selected
    | true =>
      simp only [d136372, d137579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136373 q = 0) : d137580 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136373, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136373, d137580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136378 q = 0) : d137585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136378, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136378, d137585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136379 q = 0) : d137586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136379, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136379, d137586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136380 q = 0) : d137587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136380, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136380, d137587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136418 q = 0) : d137601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136418, d137601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136418, d137601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11781 (p : Pattern) (selected : d136419 p = 0) : d137602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136376 q = 0) : d137583 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11768 q selected
    | true =>
      simp only [d136376, d137583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136377 q = 0) : d137584 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, d137584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136382 q = 0) : d137589 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136382, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136382, d137589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136383 q = 0) : d137590 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136383, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136383, d137590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136384 q = 0) : d137591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136384, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136384, d137591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136419 q = 0) : d137602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136419, d137602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136419, d137602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11782 (p : Pattern) (selected : d136422 p = 0) : d137673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136393 q = 0) : d137647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136393, d137647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11772 q selected
    | true =>
      simp only [d136393, d137647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136394 q = 0) : d137648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136394, d137648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136394, d137648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136395 q = 0) : d137649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136395, d137649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136395, d137649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136396 q = 0) : d137650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136396, d137650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136396, d137650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136397 q = 0) : d137651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136397, d137651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136397, d137651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136422 q = 0) : d137673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136422, d137673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136422, d137673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11783 (p : Pattern) (selected : d136428 p = 0) : d137679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136339 q = 0) : d137616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136339, d137616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11761 q selected
    | true =>
      simp only [d136339, d137616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11762 q selected
  have h2 (q : Pattern) (selected : d136340 q = 0) : d137617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136340, d137617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136340, d137617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136341 q = 0) : d137618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136341, d137618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136341, d137618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136342 q = 0) : d137619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136342, d137619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136342, d137619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136349 q = 0) : d137626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136349, d137626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11763 q selected
    | true =>
      simp only [d136349, d137626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11764 q selected
  have h6 (q : Pattern) (selected : d136350 q = 0) : d137627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136350, d137627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136350, d137627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136351 q = 0) : d137628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136351, d137628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136351, d137628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136363 q = 0) : d137640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136363, d137640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11766 q selected
    | true =>
      simp only [d136363, d137640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11755 q selected
  have h9 (q : Pattern) (selected : d136386 q = 0) : d137593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136386, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11769 q selected
    | true =>
      simp only [d136386, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11770 q selected
  have h10 (q : Pattern) (selected : d136387 q = 0) : d137641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136387, d137641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136387, d137641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136399 q = 0) : d137653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136399, d137653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11773 q selected
    | true =>
      simp only [d136399, d137653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136400 q = 0) : d137654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136400, d137654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136400, d137654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136401 q = 0) : d137655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136401, d137655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136401, d137655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136402 q = 0) : d137656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136402, d137656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136402, d137656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136403 q = 0) : d137657 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136403, d137657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136403, d137657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136407 q = 0) : d137661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136407, d137661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11775 q selected
    | true =>
      simp only [d136407, d137661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11776 q selected
  have h17 (q : Pattern) (selected : d136408 q = 0) : d137662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136408, d137662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136408, d137662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136409 q = 0) : d137663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136409, d137663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136409, d137663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d136410 q = 0) : d137664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136410, d137664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136410, d137664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136413 q = 0) : d137667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136413, d137667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11777 q selected
    | true =>
      simp only [d136413, d137667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11778 q selected
  have h21 (q : Pattern) (selected : d136414 q = 0) : d137668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136414, d137668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136414, d137668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d136415 q = 0) : d137669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136415, d137669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136415, d137669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136417 q = 0) : d137671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136417, d137671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11779 q selected
    | true =>
      simp only [d136417, d137671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11758 q selected
  have h24 (q : Pattern) (selected : d136420 q = 0) : d137603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136420, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11780 q selected
    | true =>
      simp only [d136420, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11781 q selected
  have h25 (q : Pattern) (selected : d136421 q = 0) : d137672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136421, d137672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d136421, d137672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d136423 q = 0) : d137674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136423, d137674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11782 q selected
    | true =>
      simp only [d136423, d137674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d136424 q = 0) : d137675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136424, d137675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d136424, d137675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d136425 q = 0) : d137676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136425, d137676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d136425, d137676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d136426 q = 0) : d137677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136426, d137677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d136426, d137677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d136427 q = 0) : d137678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136427, d137678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136427, d137678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d136428 q = 0) : d137679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136428, d137679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136428, d137679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11784 (p : Pattern) (selected : d136435 p = 0) : d137686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136316 q = 0) : d137593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11755 q selected
    | true =>
      simp only [d136316, d137593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
  have h2 (q : Pattern) (selected : d136317 q = 0) : d137594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136317, d137594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136318 q = 0) : d137595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136318, d137595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136319 q = 0) : d137596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136319, d137596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136320 q = 0) : d137597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136320, d137597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136430 q = 0) : d137681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
    | true =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136431 q = 0) : d137682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136432 q = 0) : d137683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136433 q = 0) : d137684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136434 q = 0) : d137685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136435 q = 0) : d137686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136435, d137686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136435, d137686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11785 (p : Pattern) (selected : d136441 p = 0) : d137692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136430 q = 0) : d137681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11756 q selected
    | true =>
      simp only [d136430, d137681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136431 q = 0) : d137682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136431, d137682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136432 q = 0) : d137683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136432, d137683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136433 q = 0) : d137684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136433, d137684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136434 q = 0) : d137685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136434, d137685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136436 q = 0) : d137687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136436, d137687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11759 q selected
    | true =>
      simp only [d136436, d137687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136437 q = 0) : d137688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136437, d137688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136437, d137688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136438 q = 0) : d137689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136438, d137689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136438, d137689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136439 q = 0) : d137690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136439, d137690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136439, d137690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136440 q = 0) : d137691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136440, d137691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136440, d137691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136441 q = 0) : d137692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136441, d137692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136441, d137692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11786 (p : Pattern) (selected : d136448 p = 0) : d137699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136417 q = 0) : d137671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136417, d137671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11779 q selected
    | true =>
      simp only [d136417, d137671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11758 q selected
  have h2 (q : Pattern) (selected : d136420 q = 0) : d137603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136420, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11780 q selected
    | true =>
      simp only [d136420, d137603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11781 q selected
  have h3 (q : Pattern) (selected : d136421 q = 0) : d137672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136421, d137672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136421, d137672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136423 q = 0) : d137674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136423, d137674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11782 q selected
    | true =>
      simp only [d136423, d137674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136424 q = 0) : d137675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136424, d137675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136424, d137675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136425 q = 0) : d137676 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136425, d137676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136425, d137676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136446 q = 0) : d137697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136446, d137697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136446, d137697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136447 q = 0) : d137698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136447, d137698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136447, d137698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136448 q = 0) : d137699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136448, d137699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136448, d137699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11787 (p : Pattern) (selected : d136450 p = 0) : d137701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136436 q = 0) : d137687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136436, d137687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11759 q selected
    | true =>
      simp only [d136436, d137687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136437 q = 0) : d137688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136437, d137688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136437, d137688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136438 q = 0) : d137689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136438, d137689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136438, d137689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136439 q = 0) : d137690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136439, d137690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136439, d137690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136440 q = 0) : d137691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136440, d137691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136440, d137691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136450 q = 0) : d137701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136450, d137701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136450, d137701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11788 (p : Pattern) (selected : d136465 p = 0) : d137716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136456 q = 0) : d137707 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136456, d137707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136456, d137707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6248 q selected
  have h2 (q : Pattern) (selected : d136457 q = 0) : d137708 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136457, d137708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136457, d137708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h4 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136460 q = 0) : d137711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136460, d137711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136460, d137711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136461 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h7 (q : Pattern) (selected : d136462 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136463 q = 0) : d137714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136464 q = 0) : d137715 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136464, d137715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136464, d137715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136465 q = 0) : d137716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136465, d137716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136465, d137716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11789 (p : Pattern) (selected : d136470 p = 0) : d137721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h2 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136461 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h4 (q : Pattern) (selected : d136462 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136463 q = 0) : d137714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136468 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136469 q = 0) : d137720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136469, d137720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136469, d137720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136470 q = 0) : d137721 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136470, d137721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136470, d137721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11790 (p : Pattern) (selected : d136476 p = 0) : d137727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136466 q = 0) : d137717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136466, d137717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11788 q selected
    | true =>
      simp only [d136466, d137717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136467 q = 0) : d137718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136467, d137718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136467, d137718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136471 q = 0) : d137722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136471, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11789 q selected
    | true =>
      simp only [d136471, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136472 q = 0) : d137723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136472, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136472, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136473 q = 0) : d137724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136473, d137724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136473, d137724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136474 q = 0) : d137725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136474, d137725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136474, d137725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136475 q = 0) : d137726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136475, d137726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136475, d137726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136476 q = 0) : d137727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136476, d137727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136476, d137727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11791 (p : Pattern) (selected : d136478 p = 0) : d137729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136461 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h2 (q : Pattern) (selected : d136462 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136468 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136468, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136477 q = 0) : d137728 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136477, d137728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136477, d137728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136478 q = 0) : d137729 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136478, d137729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136478, d137729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11792 (p : Pattern) (selected : d136484 p = 0) : d137735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136471 q = 0) : d137722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136471, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11789 q selected
    | true =>
      simp only [d136471, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136472 q = 0) : d137723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136472, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136472, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136479 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11791 q selected
    | true =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136480 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136481 q = 0) : d137732 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136481, d137732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136481, d137732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136482 q = 0) : d137733 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136482, d137733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136482, d137733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136483 q = 0) : d137734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136483, d137734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136483, d137734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136484 q = 0) : d137735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136484, d137735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136484, d137735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11793 (p : Pattern) (selected : d136493 p = 0) : d137721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136486 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136486, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136486, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6257 q selected
  have h2 (q : Pattern) (selected : d136487 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136487, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136487, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136488 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
  have h4 (q : Pattern) (selected : d136489 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136490 q = 0) : d137714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136490, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136490, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136491 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136492 q = 0) : d137720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136492, d137720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136492, d137720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136493 q = 0) : d137721 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136493, d137721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136493, d137721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11794 (p : Pattern) (selected : d136497 p = 0) : d137729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136488 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
  have h2 (q : Pattern) (selected : d136489 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136491 q = 0) : d137719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136491, d137719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136496 q = 0) : d137728 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136496, d137728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136496, d137728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136497 q = 0) : d137729 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136497, d137729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136497, d137729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11795 (p : Pattern) (selected : d136503 p = 0) : d137735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136494 q = 0) : d137722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136494, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11793 q selected
    | true =>
      simp only [d136494, d137722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136495 q = 0) : d137723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136495, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136495, d137723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136498 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11794 q selected
    | true =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136499 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136500 q = 0) : d137732 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136500, d137732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136500, d137732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136501 q = 0) : d137733 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136501, d137733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136501, d137733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136502 q = 0) : d137734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136502, d137734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136502, d137734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136503 q = 0) : d137735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136503, d137735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136503, d137735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11796 (p : Pattern) (selected : d136507 p = 0) : d137740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136498 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11794 q selected
    | true =>
      simp only [d136498, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136499 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136504 q = 0) : d137737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136504, d137737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136504, d137737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136505 q = 0) : d137738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136505, d137738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136505, d137738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136506 q = 0) : d137739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136506, d137739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136506, d137739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136507 q = 0) : d137740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136507, d137740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136507, d137740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11797 (p : Pattern) (selected : d5678 p = 0) : d74404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5674 q = 0) : d74400 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3386 q selected
  have h2 (q : Pattern) (selected : d5630 q = 0) : d74356 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3386 q selected
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5675 q = 0) : d74401 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5631 q = 0) : d74357 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5676 q = 0) : d74402 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5677 q = 0) : d74403 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5678 q = 0) : d74404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro11798 (p : Pattern) (selected : d136514 p = 0) : d137747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136458 q = 0) : d137709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136458, d137709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h2 (q : Pattern) (selected : d136459 q = 0) : d137710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136459, d137710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136461 q = 0) : d137712 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136461, d137712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h4 (q : Pattern) (selected : d136462 q = 0) : d137713 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136462, d137713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136463 q = 0) : d137714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136463, d137714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136510 q = 0) : d137743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136510, d137743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136510, d137743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11797 q selected
  have h7 (q : Pattern) (selected : d136511 q = 0) : d137744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136511, d137744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136511, d137744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136512 q = 0) : d137745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136512, d137745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136512, d137745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136513 q = 0) : d137746 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136513, d137746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136513, d137746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136514 q = 0) : d137747 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136514, d137747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136514, d137747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11799 (p : Pattern) (selected : d136520 p = 0) : d137753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136515 q = 0) : d137748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136515, d137748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11798 q selected
    | true =>
      simp only [d136515, d137748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136516 q = 0) : d137749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136516, d137749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136516, d137749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136517 q = 0) : d137750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136517, d137750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136517, d137750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136518 q = 0) : d137751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136518, d137751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136518, d137751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136519 q = 0) : d137752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136519, d137752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136519, d137752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136520 q = 0) : d137753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136520, d137753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136520, d137753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11800 (p : Pattern) (selected : d136526 p = 0) : d137759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136485 q = 0) : d137736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136485, d137736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11790 q selected
    | true =>
      simp only [d136485, d137736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11792 q selected
  have h2 (q : Pattern) (selected : d136508 q = 0) : d137741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136508, d137741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11795 q selected
    | true =>
      simp only [d136508, d137741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11796 q selected
  have h3 (q : Pattern) (selected : d136509 q = 0) : d137742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136509, d137742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136509, d137742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136521 q = 0) : d137754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136521, d137754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11799 q selected
    | true =>
      simp only [d136521, d137754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136522 q = 0) : d137755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136522, d137755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136522, d137755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136523 q = 0) : d137756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136523, d137756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136523, d137756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136524 q = 0) : d137757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136524, d137757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136524, d137757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136525 q = 0) : d137758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136525, d137758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136525, d137758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136526 q = 0) : d137759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136526, d137759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136526, d137759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11801 (p : Pattern) (selected : d136531 p = 0) : d137740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136479 q = 0) : d137730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11791 q selected
    | true =>
      simp only [d136479, d137730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136480 q = 0) : d137731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136480, d137731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136528 q = 0) : d137737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136528, d137737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136528, d137737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136529 q = 0) : d137738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136529, d137738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136529, d137738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136530 q = 0) : d137739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136530, d137739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136530, d137739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136531 q = 0) : d137740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136531, d137740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136531, d137740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11802 (p : Pattern) (selected : d136537 p = 0) : d137766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136532 q = 0) : d137761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136532, d137761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11801 q selected
    | true =>
      simp only [d136532, d137761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136533 q = 0) : d137762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136533, d137762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136533, d137762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136534 q = 0) : d137763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136534, d137763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136534, d137763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136535 q = 0) : d137764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136535, d137764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136535, d137764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136536 q = 0) : d137765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136536, d137765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136536, d137765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136537 q = 0) : d137766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136537, d137766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136537, d137766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11803 (p : Pattern) (selected : d136543 p = 0) : d137772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136322 q = 0) : d137599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136322, d137599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136322, d137599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11757 q selected
  have h2 (q : Pattern) (selected : d136323 q = 0) : d137600 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136323, d137600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136323, d137600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136332 q = 0) : d137609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136332, d137609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11757 q selected
    | true =>
      simp only [d136332, d137609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11760 q selected
  have h4 (q : Pattern) (selected : d136333 q = 0) : d137610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136333, d137610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136333, d137610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136334 q = 0) : d137611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136334, d137611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136334, d137611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136429 q = 0) : d137680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136429, d137680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11774 q selected
    | true =>
      simp only [d136429, d137680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11783 q selected
  have h7 (q : Pattern) (selected : d136442 q = 0) : d137693 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136442, d137693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11784 q selected
    | true =>
      simp only [d136442, d137693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11785 q selected
  have h8 (q : Pattern) (selected : d136443 q = 0) : d137694 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136443, d137694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136443, d137694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136444 q = 0) : d137695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136444, d137695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136444, d137695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d136445 q = 0) : d137696 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136445, d137696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136445, d137696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136449 q = 0) : d137700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136449, d137700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136449, d137700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11786 q selected
  have h12 (q : Pattern) (selected : d136451 q = 0) : d137702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136451, d137702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136451, d137702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11787 q selected
  have h13 (q : Pattern) (selected : d136452 q = 0) : d137703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136452, d137703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136452, d137703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136453 q = 0) : d137704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136453, d137704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136453, d137704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d136454 q = 0) : d137705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136454, d137705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d136454, d137705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d136455 q = 0) : d137706 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136455, d137706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136455, d137706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136527 q = 0) : d137760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136527, d137760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136527, d137760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11800 q selected
  have h18 (q : Pattern) (selected : d136538 q = 0) : d137767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136538, d137767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136538, d137767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11802 q selected
  have h19 (q : Pattern) (selected : d136539 q = 0) : d137768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136539, d137768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136539, d137768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136540 q = 0) : d137769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136540, d137769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136540, d137769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d136541 q = 0) : d137770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136541, d137770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d136541, d137770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d136542 q = 0) : d137771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136542, d137771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136542, d137771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136543 q = 0) : d137772 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136543, d137772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136543, d137772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11804 (p : Pattern) (selected : d136549 p = 0) : d137778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136544 q = 0) : d137773 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136544, d137773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136544, d137773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11803 q selected
  have h2 (q : Pattern) (selected : d136545 q = 0) : d137774 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136545, d137774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136545, d137774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136546 q = 0) : d137775 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136546, d137775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136546, d137775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136547 q = 0) : d137776 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136547, d137776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136547, d137776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136548 q = 0) : d137777 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136548, d137777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136548, d137777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136549 q = 0) : d137778 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136549, d137778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136549, d137778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11805 (p : Pattern) (selected : d136561 p = 0) : d137790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h2 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136556 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h4 (q : Pattern) (selected : d136557 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136558 q = 0) : d137787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136559 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136560 q = 0) : d137789 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136560, d137789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136560, d137789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136561 q = 0) : d137790 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136561, d137790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136561, d137790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11806 (p : Pattern) (selected : d136565 p = 0) : d137794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136556 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h2 (q : Pattern) (selected : d136557 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136559 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136559, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136564 q = 0) : d137793 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136564, d137793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136564, d137793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136565 q = 0) : d137794 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136565, d137794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136565, d137794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11807 (p : Pattern) (selected : d136571 p = 0) : d137800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136569 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136570 q = 0) : d137799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136570, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136570, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136571 q = 0) : d137800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136571, d137800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136571, d137800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11808 (p : Pattern) (selected : d136575 p = 0) : d137804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136573 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136574 q = 0) : d137803 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136574, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136574, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136575 q = 0) : d137804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136575, d137804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136575, d137804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11809 (p : Pattern) (selected : d136581 p = 0) : d137810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136576 q = 0) : d137805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11807 q selected
    | true =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d136577 q = 0) : d137806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136578 q = 0) : d137807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136579 q = 0) : d137808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136580 q = 0) : d137809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136581 q = 0) : d137810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136581, d137810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136581, d137810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11810 (p : Pattern) (selected : d136584 p = 0) : d137813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136569 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136570 q = 0) : d137799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136570, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136570, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136584 q = 0) : d137813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136584, d137813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136584, d137813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11811 (p : Pattern) (selected : d136585 p = 0) : d137814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136573 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136574 q = 0) : d137803 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136574, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136574, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136585 q = 0) : d137814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136585, d137814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136585, d137814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11812 (p : Pattern) (selected : d136591 p = 0) : d137820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136576 q = 0) : d137805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11807 q selected
    | true =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d136577 q = 0) : d137806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136578 q = 0) : d137807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136579 q = 0) : d137808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136580 q = 0) : d137809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136586 q = 0) : d137815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136586, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11810 q selected
    | true =>
      simp only [d136586, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11811 q selected
  have h7 (q : Pattern) (selected : d136587 q = 0) : d137816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136587, d137816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136587, d137816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136588 q = 0) : d137817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136588, d137817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136588, d137817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136589 q = 0) : d137818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136589, d137818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136589, d137818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136590 q = 0) : d137819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136590, d137819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136590, d137819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136591 q = 0) : d137820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136591, d137820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136591, d137820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11813 (p : Pattern) (selected : d136596 p = 0) : d137825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136569 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136595 q = 0) : d137824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136595, d137824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136595, d137824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136596 q = 0) : d137825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136596, d137825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136596, d137825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11814 (p : Pattern) (selected : d136598 p = 0) : d137827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136573 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136597 q = 0) : d137826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136597, d137826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136597, d137826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136598 q = 0) : d137827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136598, d137827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136598, d137827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11815 (p : Pattern) (selected : d136605 p = 0) : d137834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136603 q = 0) : d137832 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136603, d137832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136603, d137832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136604 q = 0) : d137833 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136604, d137833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136604, d137833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136605 q = 0) : d137834 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136605, d137834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136605, d137834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11816 (p : Pattern) (selected : d136608 p = 0) : d137837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136606 q = 0) : d137835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136606, d137835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136606, d137835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136607 q = 0) : d137836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136607, d137836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136607, d137836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136608 q = 0) : d137837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136608, d137837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136608, d137837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11817 (p : Pattern) (selected : d136616 p = 0) : d137845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136612 q = 0) : d137841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136612, d137841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136612, d137841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6286 q selected
  have h2 (q : Pattern) (selected : d136613 q = 0) : d137842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136613, d137842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136613, d137842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h4 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136614 q = 0) : d137843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136614, d137843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136614, d137843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136556 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h7 (q : Pattern) (selected : d136557 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136558 q = 0) : d137787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136615 q = 0) : d137844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136615, d137844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136615, d137844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136616 q = 0) : d137845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136616, d137845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136616, d137845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11818 (p : Pattern) (selected : d136622 p = 0) : d137851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136617 q = 0) : d137846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136617, d137846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11817 q selected
    | true =>
      simp only [d136617, d137846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136618 q = 0) : d137847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136618, d137847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136618, d137847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136619 q = 0) : d137848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136619, d137848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136619, d137848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136620 q = 0) : d137849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136620, d137849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136620, d137849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136621 q = 0) : d137850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136621, d137850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136621, d137850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136622 q = 0) : d137851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136622, d137851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136622, d137851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11819 (p : Pattern) (selected : d136631 p = 0) : d137790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136624 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136624, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136624, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6291 q selected
  have h2 (q : Pattern) (selected : d136625 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136625, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136625, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136626 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
  have h4 (q : Pattern) (selected : d136627 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136628 q = 0) : d137787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136628, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136628, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136629 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136630 q = 0) : d137789 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136630, d137789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136630, d137789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136631 q = 0) : d137790 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136631, d137790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136631, d137790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11820 (p : Pattern) (selected : d136635 p = 0) : d137794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136626 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
  have h2 (q : Pattern) (selected : d136627 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136629 q = 0) : d137788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136629, d137788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136634 q = 0) : d137793 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136634, d137793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136634, d137793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136635 q = 0) : d137794 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136635, d137794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136635, d137794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11821 (p : Pattern) (selected : d136641 p = 0) : d137800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136632 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136632, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11819 q selected
    | true =>
      simp only [d136632, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136633 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136633, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136633, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136638 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136638, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136638, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136639 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136639, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136639, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136640 q = 0) : d137799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136640, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136640, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136641 q = 0) : d137800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136641, d137800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136641, d137800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11822 (p : Pattern) (selected : d136645 p = 0) : d137804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136642 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136642, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136642, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136643 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136643, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136643, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136644 q = 0) : d137803 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136644, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136644, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136645 q = 0) : d137804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136645, d137804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136645, d137804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11823 (p : Pattern) (selected : d5725 p = 0) : d74451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5721 q = 0) : d74447 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3402 q selected
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5722 q = 0) : d74448 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5723 q = 0) : d74449 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5724 q = 0) : d74450 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5725 q = 0) : d74451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11824 (p : Pattern) (selected : d136652 p = 0) : d137858 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136554 q = 0) : d137783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136554, d137783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h2 (q : Pattern) (selected : d136555 q = 0) : d137784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136555, d137784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136556 q = 0) : d137785 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136556, d137785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h4 (q : Pattern) (selected : d136557 q = 0) : d137786 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136557, d137786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136558 q = 0) : d137787 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136558, d137787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136648 q = 0) : d137854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136648, d137854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136648, d137854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11823 q selected
  have h7 (q : Pattern) (selected : d136649 q = 0) : d137855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136649, d137855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136649, d137855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136650 q = 0) : d137856 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136650, d137856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136650, d137856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136651 q = 0) : d137857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136651, d137857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136651, d137857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136652 q = 0) : d137858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136652, d137858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136652, d137858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11825 (p : Pattern) (selected : d136658 p = 0) : d137864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136653 q = 0) : d137859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136653, d137859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11824 q selected
    | true =>
      simp only [d136653, d137859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136654 q = 0) : d137860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136654, d137860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136654, d137860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136655 q = 0) : d137861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136655, d137861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136655, d137861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136656 q = 0) : d137862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136656, d137862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136656, d137862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136657 q = 0) : d137863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136657, d137863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136657, d137863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136658 q = 0) : d137864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136658, d137864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136658, d137864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11826 (p : Pattern) (selected : d136664 p = 0) : d137870 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136599 q = 0) : d137828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136599, d137828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11813 q selected
    | true =>
      simp only [d136599, d137828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11814 q selected
  have h2 (q : Pattern) (selected : d136600 q = 0) : d137829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136600, d137829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136600, d137829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136601 q = 0) : d137830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136601, d137830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136601, d137830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136602 q = 0) : d137831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136602, d137831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136602, d137831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136609 q = 0) : d137838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136609, d137838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11815 q selected
    | true =>
      simp only [d136609, d137838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11816 q selected
  have h6 (q : Pattern) (selected : d136610 q = 0) : d137839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136610, d137839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136610, d137839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136611 q = 0) : d137840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136611, d137840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136611, d137840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136623 q = 0) : d137852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136623, d137852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11818 q selected
    | true =>
      simp only [d136623, d137852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11807 q selected
  have h9 (q : Pattern) (selected : d136646 q = 0) : d137805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136646, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11821 q selected
    | true =>
      simp only [d136646, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11822 q selected
  have h10 (q : Pattern) (selected : d136647 q = 0) : d137853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136647, d137853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136647, d137853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136659 q = 0) : d137865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136659, d137865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11825 q selected
    | true =>
      simp only [d136659, d137865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136660 q = 0) : d137866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136660, d137866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136660, d137866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136661 q = 0) : d137867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136661, d137867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136661, d137867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136662 q = 0) : d137868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136662, d137868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136662, d137868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136663 q = 0) : d137869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136663, d137869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136663, d137869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136664 q = 0) : d137870 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136664, d137870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136664, d137870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11827 (p : Pattern) (selected : d136665 p = 0) : d137871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136569 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136569, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136595 q = 0) : d137824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136595, d137824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136595, d137824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136665 q = 0) : d137871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136665, d137871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136665, d137871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11828 (p : Pattern) (selected : d136666 p = 0) : d137872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136573 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136573, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136597 q = 0) : d137826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136597, d137826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136597, d137826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136666 q = 0) : d137872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136666, d137872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136666, d137872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11829 (p : Pattern) (selected : d136671 p = 0) : d137877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136568 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136568, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136603 q = 0) : d137832 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136603, d137832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136603, d137832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136604 q = 0) : d137833 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136604, d137833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136604, d137833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136671 q = 0) : d137877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136671, d137877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136671, d137877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11830 (p : Pattern) (selected : d136672 p = 0) : d137878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136566 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11806 q selected
    | true =>
      simp only [d136566, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136567 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136567, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136572 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136572, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136606 q = 0) : d137835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136606, d137835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136606, d137835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136607 q = 0) : d137836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136607, d137836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136607, d137836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136672 q = 0) : d137878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136672, d137878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136672, d137878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11831 (p : Pattern) (selected : d136676 p = 0) : d137882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136617 q = 0) : d137846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136617, d137846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11817 q selected
    | true =>
      simp only [d136617, d137846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136618 q = 0) : d137847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136618, d137847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136618, d137847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136562 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11805 q selected
    | true =>
      simp only [d136562, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136563 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136563, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136619 q = 0) : d137848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136619, d137848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136619, d137848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136620 q = 0) : d137849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136620, d137849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136620, d137849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136621 q = 0) : d137850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136621, d137850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136621, d137850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136676 q = 0) : d137882 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136676, d137882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136676, d137882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11832 (p : Pattern) (selected : d136678 p = 0) : d137813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136632 q = 0) : d137791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136632, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11819 q selected
    | true =>
      simp only [d136632, d137791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136633 q = 0) : d137792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136633, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136633, d137792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136638 q = 0) : d137797 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136638, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136638, d137797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136639 q = 0) : d137798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136639, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136639, d137798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136640 q = 0) : d137799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136640, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136640, d137799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136678 q = 0) : d137813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136678, d137813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136678, d137813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11833 (p : Pattern) (selected : d136679 p = 0) : d137814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136636 q = 0) : d137795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11820 q selected
    | true =>
      simp only [d136636, d137795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136637 q = 0) : d137796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, d137796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136642 q = 0) : d137801 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136642, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136642, d137801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136643 q = 0) : d137802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136643, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136643, d137802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136644 q = 0) : d137803 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136644, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136644, d137803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136679 q = 0) : d137814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136679, d137814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136679, d137814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11834 (p : Pattern) (selected : d136682 p = 0) : d137885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136653 q = 0) : d137859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136653, d137859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11824 q selected
    | true =>
      simp only [d136653, d137859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136654 q = 0) : d137860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136654, d137860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136654, d137860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136655 q = 0) : d137861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136655, d137861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136655, d137861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136656 q = 0) : d137862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136656, d137862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136656, d137862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136657 q = 0) : d137863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136657, d137863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136657, d137863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136682 q = 0) : d137885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136682, d137885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136682, d137885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11835 (p : Pattern) (selected : d136688 p = 0) : d137891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136599 q = 0) : d137828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136599, d137828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11813 q selected
    | true =>
      simp only [d136599, d137828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11814 q selected
  have h2 (q : Pattern) (selected : d136600 q = 0) : d137829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136600, d137829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136600, d137829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136601 q = 0) : d137830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136601, d137830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136601, d137830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136602 q = 0) : d137831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136602, d137831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136602, d137831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136609 q = 0) : d137838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136609, d137838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11815 q selected
    | true =>
      simp only [d136609, d137838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11816 q selected
  have h6 (q : Pattern) (selected : d136610 q = 0) : d137839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136610, d137839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136610, d137839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136611 q = 0) : d137840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136611, d137840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136611, d137840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136623 q = 0) : d137852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136623, d137852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11818 q selected
    | true =>
      simp only [d136623, d137852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11807 q selected
  have h9 (q : Pattern) (selected : d136646 q = 0) : d137805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136646, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11821 q selected
    | true =>
      simp only [d136646, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11822 q selected
  have h10 (q : Pattern) (selected : d136647 q = 0) : d137853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136647, d137853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136647, d137853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136659 q = 0) : d137865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136659, d137865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11825 q selected
    | true =>
      simp only [d136659, d137865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d136660 q = 0) : d137866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136660, d137866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136660, d137866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d136661 q = 0) : d137867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136661, d137867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136661, d137867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136662 q = 0) : d137868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136662, d137868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136662, d137868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136663 q = 0) : d137869 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136663, d137869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136663, d137869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136667 q = 0) : d137873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136667, d137873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11827 q selected
    | true =>
      simp only [d136667, d137873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11828 q selected
  have h17 (q : Pattern) (selected : d136668 q = 0) : d137874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136668, d137874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136668, d137874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136669 q = 0) : d137875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136669, d137875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136669, d137875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d136670 q = 0) : d137876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136670, d137876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136670, d137876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136673 q = 0) : d137879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136673, d137879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11829 q selected
    | true =>
      simp only [d136673, d137879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11830 q selected
  have h21 (q : Pattern) (selected : d136674 q = 0) : d137880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136674, d137880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136674, d137880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d136675 q = 0) : d137881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136675, d137881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136675, d137881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136677 q = 0) : d137883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136677, d137883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11831 q selected
    | true =>
      simp only [d136677, d137883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11810 q selected
  have h24 (q : Pattern) (selected : d136680 q = 0) : d137815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136680, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11832 q selected
    | true =>
      simp only [d136680, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11833 q selected
  have h25 (q : Pattern) (selected : d136681 q = 0) : d137884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136681, d137884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d136681, d137884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d136683 q = 0) : d137886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136683, d137886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11834 q selected
    | true =>
      simp only [d136683, d137886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d136684 q = 0) : d137887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136684, d137887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d136684, d137887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d136685 q = 0) : d137888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136685, d137888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d136685, d137888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d136686 q = 0) : d137889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136686, d137889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d136686, d137889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d136687 q = 0) : d137890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136687, d137890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136687, d137890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d136688 q = 0) : d137891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136688, d137891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136688, d137891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11836 (p : Pattern) (selected : d136695 p = 0) : d137898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136576 q = 0) : d137805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11807 q selected
    | true =>
      simp only [d136576, d137805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
  have h2 (q : Pattern) (selected : d136577 q = 0) : d137806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136577, d137806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136578 q = 0) : d137807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136578, d137807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136579 q = 0) : d137808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136579, d137808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136580 q = 0) : d137809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136580, d137809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136690 q = 0) : d137893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
    | true =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136691 q = 0) : d137894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136692 q = 0) : d137895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136693 q = 0) : d137896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136694 q = 0) : d137897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136695 q = 0) : d137898 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136695, d137898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136695, d137898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11837 (p : Pattern) (selected : d136701 p = 0) : d137904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136690 q = 0) : d137893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11808 q selected
    | true =>
      simp only [d136690, d137893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136691 q = 0) : d137894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136691, d137894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136692 q = 0) : d137895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136692, d137895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136693 q = 0) : d137896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136693, d137896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136694 q = 0) : d137897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136694, d137897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136696 q = 0) : d137899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136696, d137899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11811 q selected
    | true =>
      simp only [d136696, d137899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136697 q = 0) : d137900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136697, d137900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136697, d137900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136698 q = 0) : d137901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136698, d137901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136698, d137901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136699 q = 0) : d137902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136699, d137902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136699, d137902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136700 q = 0) : d137903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136700, d137903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136700, d137903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136701 q = 0) : d137904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136701, d137904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136701, d137904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11838 (p : Pattern) (selected : d136708 p = 0) : d137911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136677 q = 0) : d137883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136677, d137883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11831 q selected
    | true =>
      simp only [d136677, d137883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11810 q selected
  have h2 (q : Pattern) (selected : d136680 q = 0) : d137815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136680, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11832 q selected
    | true =>
      simp only [d136680, d137815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11833 q selected
  have h3 (q : Pattern) (selected : d136681 q = 0) : d137884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136681, d137884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136681, d137884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136683 q = 0) : d137886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136683, d137886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11834 q selected
    | true =>
      simp only [d136683, d137886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136684 q = 0) : d137887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136684, d137887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136684, d137887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136685 q = 0) : d137888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136685, d137888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136685, d137888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136706 q = 0) : d137909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136706, d137909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136706, d137909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136707 q = 0) : d137910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136707, d137910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136707, d137910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136708 q = 0) : d137911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136708, d137911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136708, d137911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11839 (p : Pattern) (selected : d136710 p = 0) : d137913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136696 q = 0) : d137899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136696, d137899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11811 q selected
    | true =>
      simp only [d136696, d137899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136697 q = 0) : d137900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136697, d137900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136697, d137900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136698 q = 0) : d137901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136698, d137901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136698, d137901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136699 q = 0) : d137902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136699, d137902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136699, d137902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136700 q = 0) : d137903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136700, d137903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136700, d137903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136710 q = 0) : d137913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136710, d137913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136710, d137913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11840 (p : Pattern) (selected : d136725 p = 0) : d137928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136716 q = 0) : d137919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136716, d137919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136716, d137919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6314 q selected
  have h2 (q : Pattern) (selected : d136717 q = 0) : d137920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136717, d137920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136717, d137920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h4 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136720 q = 0) : d137923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136720, d137923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136720, d137923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136721 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h7 (q : Pattern) (selected : d136722 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136723 q = 0) : d137926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136724 q = 0) : d137927 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136724, d137927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136724, d137927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136725 q = 0) : d137928 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136725, d137928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136725, d137928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11841 (p : Pattern) (selected : d136730 p = 0) : d137933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h2 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136721 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h4 (q : Pattern) (selected : d136722 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136723 q = 0) : d137926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136728 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136729 q = 0) : d137932 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136729, d137932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136729, d137932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136730 q = 0) : d137933 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136730, d137933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136730, d137933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11842 (p : Pattern) (selected : d136736 p = 0) : d137939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136726 q = 0) : d137929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136726, d137929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11840 q selected
    | true =>
      simp only [d136726, d137929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136727 q = 0) : d137930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136727, d137930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136727, d137930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136731 q = 0) : d137934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136731, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11841 q selected
    | true =>
      simp only [d136731, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136732 q = 0) : d137935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136732, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136732, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136733 q = 0) : d137936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136733, d137936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136733, d137936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136734 q = 0) : d137937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136734, d137937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136734, d137937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136735 q = 0) : d137938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136735, d137938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136735, d137938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136736 q = 0) : d137939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136736, d137939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136736, d137939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11843 (p : Pattern) (selected : d136738 p = 0) : d137941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136721 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h2 (q : Pattern) (selected : d136722 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136728 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136728, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136737 q = 0) : d137940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136737, d137940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136737, d137940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136738 q = 0) : d137941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136738, d137941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136738, d137941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11844 (p : Pattern) (selected : d136744 p = 0) : d137947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136731 q = 0) : d137934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136731, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11841 q selected
    | true =>
      simp only [d136731, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136732 q = 0) : d137935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136732, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136732, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136739 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11843 q selected
    | true =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136740 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136741 q = 0) : d137944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136741, d137944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136741, d137944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136742 q = 0) : d137945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136742, d137945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136742, d137945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136743 q = 0) : d137946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136743, d137946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136743, d137946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136744 q = 0) : d137947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136744, d137947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136744, d137947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11845 (p : Pattern) (selected : d136753 p = 0) : d137933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136746 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136746, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136746, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6323 q selected
  have h2 (q : Pattern) (selected : d136747 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136747, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136747, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136748 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
  have h4 (q : Pattern) (selected : d136749 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136750 q = 0) : d137926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136750, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136750, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136751 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136752 q = 0) : d137932 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136752, d137932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136752, d137932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136753 q = 0) : d137933 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136753, d137933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136753, d137933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11846 (p : Pattern) (selected : d136757 p = 0) : d137941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136748 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
  have h2 (q : Pattern) (selected : d136749 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136751 q = 0) : d137931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136751, d137931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136756 q = 0) : d137940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136756, d137940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136756, d137940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136757 q = 0) : d137941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136757, d137941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136757, d137941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11847 (p : Pattern) (selected : d136763 p = 0) : d137947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136754 q = 0) : d137934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136754, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11845 q selected
    | true =>
      simp only [d136754, d137934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136755 q = 0) : d137935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136755, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136755, d137935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136758 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11846 q selected
    | true =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136759 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136760 q = 0) : d137944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136760, d137944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136760, d137944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136761 q = 0) : d137945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136761, d137945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136761, d137945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136762 q = 0) : d137946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136762, d137946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136762, d137946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136763 q = 0) : d137947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136763, d137947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136763, d137947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11848 (p : Pattern) (selected : d136767 p = 0) : d137952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136758 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11846 q selected
    | true =>
      simp only [d136758, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136759 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136764 q = 0) : d137949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136764, d137949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136764, d137949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136765 q = 0) : d137950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136765, d137950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136765, d137950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136766 q = 0) : d137951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136766, d137951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136766, d137951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136767 q = 0) : d137952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136767, d137952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136767, d137952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11849 (p : Pattern) (selected : d5769 p = 0) : d74495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5765 q = 0) : d74491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3402 q selected
  have h2 (q : Pattern) (selected : d5721 q = 0) : d74447 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3402 q selected
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d5766 q = 0) : d74492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5722 q = 0) : d74448 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5767 q = 0) : d74493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5768 q = 0) : d74494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5769 q = 0) : d74495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro11850 (p : Pattern) (selected : d136774 p = 0) : d137959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136718 q = 0) : d137921 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136718, d137921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h2 (q : Pattern) (selected : d136719 q = 0) : d137922 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136719, d137922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136721 q = 0) : d137924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136721, d137924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h4 (q : Pattern) (selected : d136722 q = 0) : d137925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136722, d137925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136723 q = 0) : d137926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136723, d137926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136770 q = 0) : d137955 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136770, d137955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136770, d137955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11849 q selected
  have h7 (q : Pattern) (selected : d136771 q = 0) : d137956 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136771, d137956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136771, d137956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136772 q = 0) : d137957 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136772, d137957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136772, d137957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d136773 q = 0) : d137958 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136773, d137958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136773, d137958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136774 q = 0) : d137959 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136774, d137959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136774, d137959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11851 (p : Pattern) (selected : d136780 p = 0) : d137965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136775 q = 0) : d137960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136775, d137960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11850 q selected
    | true =>
      simp only [d136775, d137960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136776 q = 0) : d137961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136776, d137961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136776, d137961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136777 q = 0) : d137962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136777, d137962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136777, d137962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136778 q = 0) : d137963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136778, d137963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136778, d137963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136779 q = 0) : d137964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136779, d137964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136779, d137964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136780 q = 0) : d137965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136780, d137965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136780, d137965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11852 (p : Pattern) (selected : d136786 p = 0) : d137971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136745 q = 0) : d137948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136745, d137948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11842 q selected
    | true =>
      simp only [d136745, d137948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11844 q selected
  have h2 (q : Pattern) (selected : d136768 q = 0) : d137953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136768, d137953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11847 q selected
    | true =>
      simp only [d136768, d137953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11848 q selected
  have h3 (q : Pattern) (selected : d136769 q = 0) : d137954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136769, d137954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136769, d137954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136781 q = 0) : d137966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136781, d137966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11851 q selected
    | true =>
      simp only [d136781, d137966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136782 q = 0) : d137967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136782, d137967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136782, d137967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136783 q = 0) : d137968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136783, d137968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136783, d137968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136784 q = 0) : d137969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136784, d137969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136784, d137969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136785 q = 0) : d137970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136785, d137970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136785, d137970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136786 q = 0) : d137971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136786, d137971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136786, d137971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11853 (p : Pattern) (selected : d136791 p = 0) : d137952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136739 q = 0) : d137942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11843 q selected
    | true =>
      simp only [d136739, d137942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136740 q = 0) : d137943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136740, d137943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136788 q = 0) : d137949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136788, d137949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136788, d137949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136789 q = 0) : d137950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136789, d137950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136789, d137950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136790 q = 0) : d137951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136790, d137951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136790, d137951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136791 q = 0) : d137952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136791, d137952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136791, d137952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11854 (p : Pattern) (selected : d136797 p = 0) : d137978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136792 q = 0) : d137973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136792, d137973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11853 q selected
    | true =>
      simp only [d136792, d137973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136793 q = 0) : d137974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136793, d137974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136793, d137974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136794 q = 0) : d137975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136794, d137975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136794, d137975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136795 q = 0) : d137976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136795, d137976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136795, d137976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136796 q = 0) : d137977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136796, d137977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136796, d137977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136797 q = 0) : d137978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136797, d137978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136797, d137978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11855 (p : Pattern) (selected : d136803 p = 0) : d137984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136582 q = 0) : d137811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136582, d137811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136582, d137811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11809 q selected
  have h2 (q : Pattern) (selected : d136583 q = 0) : d137812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136583, d137812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136583, d137812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136592 q = 0) : d137821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136592, d137821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11809 q selected
    | true =>
      simp only [d136592, d137821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11812 q selected
  have h4 (q : Pattern) (selected : d136593 q = 0) : d137822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136593, d137822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136593, d137822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136594 q = 0) : d137823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136594, d137823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136594, d137823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136689 q = 0) : d137892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136689, d137892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11826 q selected
    | true =>
      simp only [d136689, d137892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11835 q selected
  have h7 (q : Pattern) (selected : d136702 q = 0) : d137905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136702, d137905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11836 q selected
    | true =>
      simp only [d136702, d137905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11837 q selected
  have h8 (q : Pattern) (selected : d136703 q = 0) : d137906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136703, d137906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136703, d137906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136704 q = 0) : d137907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136704, d137907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136704, d137907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d136705 q = 0) : d137908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136705, d137908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136705, d137908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136709 q = 0) : d137912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136709, d137912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136709, d137912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11838 q selected
  have h12 (q : Pattern) (selected : d136711 q = 0) : d137914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136711, d137914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136711, d137914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11839 q selected
  have h13 (q : Pattern) (selected : d136712 q = 0) : d137915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136712, d137915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136712, d137915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136713 q = 0) : d137916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136713, d137916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136713, d137916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d136714 q = 0) : d137917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136714, d137917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d136714, d137917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d136715 q = 0) : d137918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136715, d137918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136715, d137918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136787 q = 0) : d137972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136787, d137972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136787, d137972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11852 q selected
  have h18 (q : Pattern) (selected : d136798 q = 0) : d137979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136798, d137979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136798, d137979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11854 q selected
  have h19 (q : Pattern) (selected : d136799 q = 0) : d137980 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136799, d137980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136799, d137980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d136800 q = 0) : d137981 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136800, d137981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d136800, d137981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d136801 q = 0) : d137982 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136801, d137982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d136801, d137982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d136802 q = 0) : d137983 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136802, d137983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d136802, d137983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d136803 q = 0) : d137984 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136803, d137984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136803, d137984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11856 (p : Pattern) (selected : d136809 p = 0) : d137990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136804 q = 0) : d137985 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136804, d137985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136804, d137985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11855 q selected
  have h2 (q : Pattern) (selected : d136805 q = 0) : d137986 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136805, d137986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136805, d137986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136806 q = 0) : d137987 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136806, d137987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136806, d137987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136807 q = 0) : d137988 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136807, d137988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136807, d137988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136808 q = 0) : d137989 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136808, d137989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136808, d137989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136809 q = 0) : d137990 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136809, d137990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136809, d137990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11857 (p : Pattern) (selected : d136815 p = 0) : d137996 p = 1 := by
  have h0 (q : Pattern) (selected : d135776 q = 0) : d137149 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d135776, d137149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11620 q selected
    | true =>
      simp only [d135776, d137149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11648 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d136033 q = 0) : d137358 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136033, d137358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136033, d137358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11700 q selected
  have h3 (q : Pattern) (selected : d136034 q = 0) : d137359 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136034, d137359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136034, d137359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136291 q = 0) : d137568 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136291, d137568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136291, d137568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11752 q selected
  have h5 (q : Pattern) (selected : d136292 q = 0) : d137569 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136292, d137569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136292, d137569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136293 q = 0) : d137570 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136293, d137570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136293, d137570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136550 q = 0) : d137779 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136550, d137779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136550, d137779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11804 q selected
  have h8 (q : Pattern) (selected : d136551 q = 0) : d137780 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136551, d137780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136551, d137780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136552 q = 0) : d137781 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136552, d137781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136552, d137781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136553 q = 0) : d137782 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d136553, d137782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136553, d137782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136810 q = 0) : d137991 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136810, d137991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136810, d137991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11856 q selected
  have h12 (q : Pattern) (selected : d136811 q = 0) : d137992 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136811, d137992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136811, d137992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136812 q = 0) : d137993 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136812, d137993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136812, d137993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136813 q = 0) : d137994 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d136813, d137994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136813, d137994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136814 q = 0) : d137995 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d136814, d137995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136814, d137995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136815 q = 0) : d137996 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d136815, d137996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136815, d137996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro11858 (p : Pattern) (selected : d136821 p = 0) : d138002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136816 q = 0) : d137997 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d136816, d137997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11857 q selected
    | true =>
      simp only [d136816, d137997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136817 q = 0) : d137998 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d136817, d137998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136817, d137998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136818 q = 0) : d137999 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d136818, d137999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136818, d137999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136819 q = 0) : d138000 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d136819, d138000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136819, d138000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136820 q = 0) : d138001 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d136820, d138001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136820, d138001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136821 q = 0) : d138002 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d136821, d138002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136821, d138002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11859 (p : Pattern) (selected : d136827 p = 0) : d138008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136822 q = 0) : d138003 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d136822, d138003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11858 q selected
    | true =>
      simp only [d136822, d138003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136823 q = 0) : d138004 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d136823, d138004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136823, d138004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136824 q = 0) : d138005 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d136824, d138005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136824, d138005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136825 q = 0) : d138006 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d136825, d138006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136825, d138006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136826 q = 0) : d138007 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d136826, d138007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136826, d138007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136827 q = 0) : d138008 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d136827, d138008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136827, d138008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11860 (p : Pattern) (selected : d136833 p = 0) : d138014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136828 q = 0) : d138009 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d136828, d138009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11859 q selected
    | true =>
      simp only [d136828, d138009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136829 q = 0) : d138010 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d136829, d138010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136829, d138010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136830 q = 0) : d138011 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d136830, d138011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136830, d138011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136831 q = 0) : d138012 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d136831, d138012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136831, d138012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136832 q = 0) : d138013 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d136832, d138013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136832, d138013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136833 q = 0) : d138014 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d136833, d138014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136833, d138014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11861 (p : Pattern) (selected : d136839 p = 0) : d138020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136834 q = 0) : d138015 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d136834, d138015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11860 q selected
    | true =>
      simp only [d136834, d138015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136835 q = 0) : d138016 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d136835, d138016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136835, d138016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136836 q = 0) : d138017 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d136836, d138017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136836, d138017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136837 q = 0) : d138018 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d136837, d138018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136837, d138018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136838 q = 0) : d138019 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d136838, d138019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136838, d138019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136839 q = 0) : d138020 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d136839, d138020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136839, d138020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11862 (p : Pattern) (selected : d136845 p = 0) : d138026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136840 q = 0) : d138021 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d136840, d138021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11861 q selected
    | true =>
      simp only [d136840, d138021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136841 q = 0) : d138022 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d136841, d138022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136841, d138022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136842 q = 0) : d138023 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d136842, d138023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136842, d138023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136843 q = 0) : d138024 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d136843, d138024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136843, d138024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136844 q = 0) : d138025 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d136844, d138025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136844, d138025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136845 q = 0) : d138026 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d136845, d138026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136845, d138026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11863 (p : Pattern) (selected : d136851 p = 0) : d138032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136846 q = 0) : d138027 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d136846, d138027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11862 q selected
    | true =>
      simp only [d136846, d138027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136847 q = 0) : d138028 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d136847, d138028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136847, d138028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136848 q = 0) : d138029 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d136848, d138029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136848, d138029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136849 q = 0) : d138030 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d136849, d138030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136849, d138030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136850 q = 0) : d138031 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d136850, d138031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136850, d138031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136851 q = 0) : d138032 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d136851, d138032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136851, d138032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11864 (p : Pattern) (selected : d136857 p = 0) : d138038 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d136852 q = 0) : d138033 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d136852, d138033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11863 q selected
    | true =>
      simp only [d136852, d138033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136853 q = 0) : d138034 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d136853, d138034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136853, d138034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136854 q = 0) : d138035 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d136854, d138035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136854, d138035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136855 q = 0) : d138036 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d136855, d138036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136855, d138036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136856 q = 0) : d138037 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d136856, d138037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136856, d138037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136857 q = 0) : d138038 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d136857, d138038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136857, d138038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11865 (p : Pattern) (selected : d135538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
  have h2 (q : Pattern) (selected : d135535 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135536 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135537 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135538 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11866 (p : Pattern) (selected : d135544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11865 q selected
    | true =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11867 (p : Pattern) (selected : d135550 p = 1) : d139462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135515 q = 1) : d135515 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135521 q = 1) : d135521 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135533 q = 1) : d135533 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
    | true =>
      simp only [d135545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135546 q = 1) : d139458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135546, d139458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135546, d139458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135445 q = 1) : d135445 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d135547 q = 1) : d139459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135547, d139459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135547, d139459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135548 q = 1) : d139460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135548, d139460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135548, d139460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135549 q = 1) : d139461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135549, d139461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135549, d139461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135550 q = 1) : d139462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135550, d139462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135550, d139462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11868 (p : Pattern) (selected : d135562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11865 q selected
    | true =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11869 (p : Pattern) (selected : d135568 p = 1) : d139467 p = 1 := by
  have h0 (q : Pattern) (selected : d135515 q = 1) : d135515 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135521 q = 1) : d135521 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135533 q = 1) : d135533 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
    | true =>
      simp only [d135545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135546 q = 1) : d139458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135546, d139458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135546, d139458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135445 q = 1) : d135445 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d135547 q = 1) : d139459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135547, d139459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135547, d139459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135548 q = 1) : d139460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135548, d139460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135548, d139460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135549 q = 1) : d139461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135549, d139461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135549, d139461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135555 q = 1) : d135555 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d135559 q = 1) : d135559 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d135561 q = 1) : d135561 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d135563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
    | true =>
      simp only [d135563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d135564 q = 1) : d139463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135564, d139463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d135564, d139463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d135452 q = 1) : d135452 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d135565 q = 1) : d139464 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135565, d139464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d135565, d139464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d135566 q = 1) : d139465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135566, d139465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135566, d139465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135567 q = 1) : d139466 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135567, d139466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135567, d139466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d135568 q = 1) : d139467 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135568, d139467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135568, d139467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11870 (p : Pattern) (selected : d135577 p = 1) : d139474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135561 q = 1) : d135561 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
    | true =>
      simp only [d135563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135564 q = 1) : d139463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135564, d139463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135564, d139463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135452 q = 1) : d135452 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135565 q = 1) : d139464 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135565, d139464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135565, d139464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135575 q = 1) : d139472 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135575, d139472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135575, d139472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135576 q = 1) : d139473 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135576, d139473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135576, d139473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135577 q = 1) : d139474 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135577, d139474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135577, d139474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11871 (p : Pattern) (selected : d135599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
  have h2 (q : Pattern) (selected : d135596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11872 (p : Pattern) (selected : d135605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11871 q selected
    | true =>
      simp only [d135600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11873 (p : Pattern) (selected : d135611 p = 1) : d139484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135594 q = 1) : d135594 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11872 q selected
    | true =>
      simp only [d135606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d135607 q = 1) : d139480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135607, d139480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135607, d139480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135479 q = 1) : d135479 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135608 q = 1) : d139481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135608, d139481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135608, d139481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135609 q = 1) : d139482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135609, d139482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135609, d139482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135610 q = 1) : d139483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135610, d139483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135610, d139483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135611 q = 1) : d139484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135611, d139484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135611, d139484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11874 (p : Pattern) (selected : d135617 p = 1) : d139490 p = 1 := by
  have h0 (q : Pattern) (selected : d135509 q = 1) : d135509 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135569 q = 1) : d139468 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135569, d139468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11867 q selected
    | true =>
      simp only [d135569, d139468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11869 q selected
  have h2 (q : Pattern) (selected : d135571 q = 1) : d135571 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135572 q = 1) : d139469 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135572, d139469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135572, d139469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135573 q = 1) : d139470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135573, d139470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135573, d139470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135574 q = 1) : d139471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135574, d139471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135574, d139471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135578 q = 1) : d139475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135578, d139475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135578, d139475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11870 q selected
  have h8 (q : Pattern) (selected : d135579 q = 1) : d139476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135579, d139476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135579, d139476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d135580 q = 1) : d139477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135580, d139477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135580, d139477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d135581 q = 1) : d139478 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135581, d139478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135581, d139478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d135582 q = 1) : d139479 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135582, d139479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135582, d139479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d135612 q = 1) : d139485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135612, d139485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135612, d139485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11873 q selected
  have h13 (q : Pattern) (selected : d135613 q = 1) : d139486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135613, d139486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d135613, d139486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d135614 q = 1) : d139487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135614, d139487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135614, d139487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d135615 q = 1) : d139488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135615, d139488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d135615, d139488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d135616 q = 1) : d139489 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135616, d139489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135616, d139489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d135617 q = 1) : d139490 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d135617, d139490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135617, d139490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro11875 (p : Pattern) (selected : d135623 p = 1) : d139496 p = 1 := by
  have h0 (q : Pattern) (selected : d135494 q = 1) : d135494 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135618 q = 1) : d139491 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d135618, d139491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135618, d139491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11874 q selected
  have h3 (q : Pattern) (selected : d135619 q = 1) : d139492 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d135619, d139492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135619, d139492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135620 q = 1) : d139493 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d135620, d139493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135620, d139493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135621 q = 1) : d139494 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d135621, d139494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135621, d139494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135622 q = 1) : d139495 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d135622, d139495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135622, d139495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135623 q = 1) : d139496 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d135623, d139496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135623, d139496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro11876 (p : Pattern) (selected : d135667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135663 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6358 q selected
  have h2 (q : Pattern) (selected : d135664 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
  have h4 (q : Pattern) (selected : d135535 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135665 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135536 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135666 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135667 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11877 (p : Pattern) (selected : d135673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135668 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11876 q selected
    | true =>
      simp only [d135668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135669 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11865 q selected
    | true =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135670 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135671 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135672 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135673 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11878 (p : Pattern) (selected : d135685 p = 1) : d139501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135644 q = 1) : d135644 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135650 q = 1) : d135650 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135662 q = 1) : d135662 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11877 q selected
    | true =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
  have h5 (q : Pattern) (selected : d135675 q = 1) : d139497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135675, d139497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135675, d139497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135681 q = 1) : d135681 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d135682 q = 1) : d139498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135682, d139498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135682, d139498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135683 q = 1) : d139499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135683, d139499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135683, d139499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135684 q = 1) : d139500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135684, d139500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135684, d139500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135685 q = 1) : d139501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135685, d139501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135685, d139501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11879 (p : Pattern) (selected : d135697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135668 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11876 q selected
    | true =>
      simp only [d135668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135669 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11865 q selected
    | true =>
      simp only [d135539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135670 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135671 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135672 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11880 (p : Pattern) (selected : d135706 p = 1) : d139506 p = 1 := by
  have h0 (q : Pattern) (selected : d135644 q = 1) : d135644 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135650 q = 1) : d135650 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135662 q = 1) : d135662 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11877 q selected
    | true =>
      simp only [d135674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11866 q selected
  have h4 (q : Pattern) (selected : d135675 q = 1) : d139497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135675, d139497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135675, d139497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135681 q = 1) : d135681 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d135682 q = 1) : d139498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135682, d139498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135682, d139498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135683 q = 1) : d139499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135683, d139499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135683, d139499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135684 q = 1) : d139500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135684, d139500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135684, d139500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135690 q = 1) : d135690 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d135694 q = 1) : d135694 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d135696 q = 1) : d135696 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d135698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11879 q selected
    | true =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
  have h13 (q : Pattern) (selected : d135699 q = 1) : d139502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135699, d139502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135699, d139502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135702 q = 1) : d135702 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d135703 q = 1) : d139503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135703, d139503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135703, d139503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135704 q = 1) : d139504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135704, d139504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135704, d139504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d135705 q = 1) : d139505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135705, d139505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135705, d139505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135706 q = 1) : d139506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135706, d139506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135706, d139506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11881 (p : Pattern) (selected : d135715 p = 1) : d139513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135696 q = 1) : d135696 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11879 q selected
    | true =>
      simp only [d135698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11868 q selected
  have h3 (q : Pattern) (selected : d135699 q = 1) : d139502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135699, d139502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135699, d139502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135702 q = 1) : d135702 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135703 q = 1) : d139503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135703, d139503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135703, d139503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135713 q = 1) : d139511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135713, d139511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135713, d139511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135714 q = 1) : d139512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135714, d139512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135714, d139512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135715 q = 1) : d139513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135715, d139513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135715, d139513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11882 (p : Pattern) (selected : d135739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6365 q selected
  have h2 (q : Pattern) (selected : d135736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135595 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
  have h4 (q : Pattern) (selected : d135596 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135738 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135739 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11883 (p : Pattern) (selected : d135745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11882 q selected
    | true =>
      simp only [d135740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11871 q selected
    | true =>
      simp only [d135600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135742 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135743 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135744 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11884 (p : Pattern) (selected : d135757 p = 1) : d139523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135734 q = 1) : d135734 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11883 q selected
    | true =>
      simp only [d135746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11872 q selected
  have h3 (q : Pattern) (selected : d135747 q = 1) : d139519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135747, d139519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135747, d139519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135753 q = 1) : d135753 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135754 q = 1) : d139520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135754, d139520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135754, d139520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135755 q = 1) : d139521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135755, d139521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135755, d139521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135756 q = 1) : d139522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135756, d139522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135756, d139522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135757 q = 1) : d139523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135757, d139523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135757, d139523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11885 (p : Pattern) (selected : d135769 p = 1) : d139529 p = 1 := by
  have h0 (q : Pattern) (selected : d135638 q = 1) : d135638 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135707 q = 1) : d139507 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135707, d139507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11878 q selected
    | true =>
      simp only [d135707, d139507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11880 q selected
  have h2 (q : Pattern) (selected : d135709 q = 1) : d135709 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135710 q = 1) : d139508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135710, d139508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135710, d139508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135711 q = 1) : d139509 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135711, d139509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135711, d139509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135712 q = 1) : d139510 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135712, d139510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135712, d139510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135716 q = 1) : d139514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135716, d139514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135716, d139514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11881 q selected
  have h8 (q : Pattern) (selected : d135718 q = 1) : d135718 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d135719 q = 1) : d139515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135719, d139515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135719, d139515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135720 q = 1) : d139516 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135720, d139516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135720, d139516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d135721 q = 1) : d139517 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135721, d139517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135721, d139517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d135722 q = 1) : d139518 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135722, d139518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135722, d139518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d135758 q = 1) : d139524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135758, d139524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135758, d139524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11884 q selected
  have h14 (q : Pattern) (selected : d135764 q = 1) : d135764 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d135765 q = 1) : d139525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135765, d139525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135765, d139525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135766 q = 1) : d139526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135766, d139526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d135766, d139526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d135767 q = 1) : d139527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135767, d139527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d135767, d139527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d135768 q = 1) : d139528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135768, d139528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d135768, d139528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d135769 q = 1) : d139529 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d135769, d139529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d135769, d139529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11886 (p : Pattern) (selected : d135775 p = 1) : d139535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135770 q = 1) : d139530 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d135770, d139530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135770, d139530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11885 q selected
  have h2 (q : Pattern) (selected : d135771 q = 1) : d139531 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d135771, d139531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135771, d139531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135772 q = 1) : d139532 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d135772, d139532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135772, d139532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135773 q = 1) : d139533 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d135773, d139533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135773, d139533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135774 q = 1) : d139534 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d135774, d139534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135774, d139534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135775 q = 1) : d139535 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d135775, d139535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135775, d139535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11887 (p : Pattern) (selected : d135854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135847 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6371 q selected
  have h2 (q : Pattern) (selected : d135848 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135849 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
  have h4 (q : Pattern) (selected : d135850 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135851 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135852 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135853 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135854 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11888 (p : Pattern) (selected : d135858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135849 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
  have h2 (q : Pattern) (selected : d135850 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135852 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11889 (p : Pattern) (selected : d135864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11887 q selected
    | true =>
      simp only [d135855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135856 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11888 q selected
    | true =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135861 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135862 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11890 (p : Pattern) (selected : d135868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11888 q selected
    | true =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11891 (p : Pattern) (selected : d135887 p = 1) : d139541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135825 q = 1) : d135825 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135834 q = 1) : d135834 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135846 q = 1) : d135846 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d135869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11889 q selected
    | true =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11890 q selected
  have h5 (q : Pattern) (selected : d135870 q = 1) : d139537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135870, d139537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135870, d139537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135883 q = 1) : d135883 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d135884 q = 1) : d139538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135884, d139538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135884, d139538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135885 q = 1) : d139539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135885, d139539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135885, d139539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135886 q = 1) : d139540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135886, d139540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135886, d139540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135887 q = 1) : d139541 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135887, d139541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135887, d139541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11892 (p : Pattern) (selected : d135901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11887 q selected
    | true =>
      simp only [d135855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135856 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11888 q selected
    | true =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135861 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135862 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11893 (p : Pattern) (selected : d135902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11888 q selected
    | true =>
      simp only [d135859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11894 (p : Pattern) (selected : d135911 p = 1) : d139546 p = 1 := by
  have h0 (q : Pattern) (selected : d135825 q = 1) : d135825 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135834 q = 1) : d135834 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135846 q = 1) : d135846 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11889 q selected
    | true =>
      simp only [d135869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11890 q selected
  have h4 (q : Pattern) (selected : d135870 q = 1) : d139537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135870, d139537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135870, d139537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135883 q = 1) : d135883 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d135884 q = 1) : d139538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135884, d139538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135884, d139538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135885 q = 1) : d139539 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135885, d139539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135885, d139539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135886 q = 1) : d139540 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135886, d139540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135886, d139540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d135893 q = 1) : d135893 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d135898 q = 1) : d135898 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d135900 q = 1) : d135900 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d135903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11892 q selected
    | true =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11893 q selected
  have h13 (q : Pattern) (selected : d135904 q = 1) : d139542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135904, d139542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d135904, d139542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d135907 q = 1) : d135907 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d135908 q = 1) : d139543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135908, d139543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d135908, d139543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d135909 q = 1) : d139544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135909, d139544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135909, d139544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d135910 q = 1) : d139545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135910, d139545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135910, d139545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d135911 q = 1) : d139546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135911, d139546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d135911, d139546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11895 (p : Pattern) (selected : d135931 p = 1) : d139553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135900 q = 1) : d135900 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11892 q selected
    | true =>
      simp only [d135903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11893 q selected
  have h3 (q : Pattern) (selected : d135904 q = 1) : d139542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135904, d139542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135904, d139542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d135907 q = 1) : d135907 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135908 q = 1) : d139543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d135908, d139543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135908, d139543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135929 q = 1) : d139551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d135929, d139551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135929, d139551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135930 q = 1) : d139552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d135930, d139552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135930, d139552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135931 q = 1) : d139553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d135931, d139553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135931, d139553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11896 (p : Pattern) (selected : d135976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135969 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6382 q selected
  have h2 (q : Pattern) (selected : d135970 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135971 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
  have h4 (q : Pattern) (selected : d135972 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135973 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135974 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d135976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11897 (p : Pattern) (selected : d135980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135971 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d135971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
  have h2 (q : Pattern) (selected : d135972 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d135972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135974 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d135974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d135979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d135980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11898 (p : Pattern) (selected : d135986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11896 q selected
    | true =>
      simp only [d135977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11897 q selected
    | true =>
      simp only [d135981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d135983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d135985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d135986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11899 (p : Pattern) (selected : d135990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d135981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11897 q selected
    | true =>
      simp only [d135981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d135982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d135982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d135987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d135987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d135988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d135988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d135989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d135990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d135990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d135990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11900 (p : Pattern) (selected : d136009 p = 1) : d139563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135968 q = 1) : d135968 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d135991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d135991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11898 q selected
    | true =>
      simp only [d135991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11899 q selected
  have h3 (q : Pattern) (selected : d135992 q = 1) : d139559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d135992, d139559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135992, d139559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136005 q = 1) : d136005 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136006 q = 1) : d139560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136006, d139560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136006, d139560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136007 q = 1) : d139561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136007, d139561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136007, d139561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136008 q = 1) : d139562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136008, d139562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136008, d139562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136009 q = 1) : d139563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136009, d139563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136009, d139563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11901 (p : Pattern) (selected : d136026 p = 1) : d139569 p = 1 := by
  have h0 (q : Pattern) (selected : d135817 q = 1) : d135817 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d135912 q = 1) : d139547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135912, d139547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11891 q selected
    | true =>
      simp only [d135912, d139547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11894 q selected
  have h2 (q : Pattern) (selected : d135925 q = 1) : d135925 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d135926 q = 1) : d139548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135926, d139548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d135926, d139548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d135927 q = 1) : d139549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135927, d139549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d135927, d139549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d135928 q = 1) : d139550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135928, d139550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d135928, d139550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d135932 q = 1) : d139554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d135932, d139554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135932, d139554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11895 q selected
  have h8 (q : Pattern) (selected : d135934 q = 1) : d135934 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d135935 q = 1) : d139555 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d135935, d139555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d135935, d139555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d135936 q = 1) : d139556 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d135936, d139556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d135936, d139556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d135937 q = 1) : d139557 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d135937, d139557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d135937, d139557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d135938 q = 1) : d139558 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d135938, d139558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d135938, d139558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136010 q = 1) : d139564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136010, d139564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136010, d139564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11900 q selected
  have h14 (q : Pattern) (selected : d136021 q = 1) : d136021 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136022 q = 1) : d139565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136022, d139565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136022, d139565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136023 q = 1) : d139566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136023, d139566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136023, d139566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d136024 q = 1) : d139567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136024, d139567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136024, d139567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d136025 q = 1) : d139568 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136025, d139568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136025, d139568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d136026 q = 1) : d139569 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136026, d139569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d136026, d139569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11902 (p : Pattern) (selected : d136032 p = 1) : d139575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136027 q = 1) : d139570 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136027, d139570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136027, d139570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11901 q selected
  have h2 (q : Pattern) (selected : d136028 q = 1) : d139571 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136028, d139571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136028, d139571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136029 q = 1) : d139572 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136029, d139572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136029, d139572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136030 q = 1) : d139573 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136030, d139573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136030, d139573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136031 q = 1) : d139574 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136031, d139574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136031, d139574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136032 q = 1) : d139575 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136032, d139575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136032, d139575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11903 (p : Pattern) (selected : d136112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136105 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6391 q selected
  have h2 (q : Pattern) (selected : d136106 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
  have h4 (q : Pattern) (selected : d136108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136110 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136112 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11904 (p : Pattern) (selected : d136116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
  have h2 (q : Pattern) (selected : d136108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136110 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136115 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136116 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11905 (p : Pattern) (selected : d136122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136113 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11903 q selected
    | true =>
      simp only [d136113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136114 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136119 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136120 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136121 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11906 (p : Pattern) (selected : d136126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136123 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11907 (p : Pattern) (selected : d136145 p = 1) : d139582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136083 q = 1) : d136083 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136092 q = 1) : d136092 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136104 q = 1) : d136104 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d136127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11905 q selected
    | true =>
      simp only [d136127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11906 q selected
  have h5 (q : Pattern) (selected : d136128 q = 1) : d139578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136128, d139578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136128, d139578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136141 q = 1) : d136141 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d136142 q = 1) : d139579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136142, d139579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136142, d139579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136143 q = 1) : d139580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136143, d139580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136143, d139580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136144 q = 1) : d139581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136144, d139581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136144, d139581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136145 q = 1) : d139582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136145, d139582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136145, d139582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11908 (p : Pattern) (selected : d136159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136113 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11903 q selected
    | true =>
      simp only [d136113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136114 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136119 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136120 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136121 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136159 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11909 (p : Pattern) (selected : d136160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11904 q selected
    | true =>
      simp only [d136117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136123 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136160 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11910 (p : Pattern) (selected : d136169 p = 1) : d139587 p = 1 := by
  have h0 (q : Pattern) (selected : d136083 q = 1) : d136083 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136092 q = 1) : d136092 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136104 q = 1) : d136104 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11905 q selected
    | true =>
      simp only [d136127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11906 q selected
  have h4 (q : Pattern) (selected : d136128 q = 1) : d139578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136128, d139578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136128, d139578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136141 q = 1) : d136141 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d136142 q = 1) : d139579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136142, d139579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136142, d139579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136143 q = 1) : d139580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136143, d139580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136143, d139580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136144 q = 1) : d139581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136144, d139581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136144, d139581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136151 q = 1) : d136151 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d136156 q = 1) : d136156 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d136158 q = 1) : d136158 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d136161 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11908 q selected
    | true =>
      simp only [d136161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11909 q selected
  have h13 (q : Pattern) (selected : d136162 q = 1) : d139583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136162, d139583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136162, d139583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136165 q = 1) : d136165 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136166 q = 1) : d139584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136166, d139584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136166, d139584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136167 q = 1) : d139585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136167, d139585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136167, d139585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136168 q = 1) : d139586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136168, d139586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136168, d139586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136169 q = 1) : d139587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136169, d139587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136169, d139587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11911 (p : Pattern) (selected : d136189 p = 1) : d139594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136158 q = 1) : d136158 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136161 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11908 q selected
    | true =>
      simp only [d136161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11909 q selected
  have h3 (q : Pattern) (selected : d136162 q = 1) : d139583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136162, d139583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136162, d139583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136165 q = 1) : d136165 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136166 q = 1) : d139584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136166, d139584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136166, d139584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136187 q = 1) : d139592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136187, d139592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136187, d139592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136188 q = 1) : d139593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136188, d139593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136188, d139593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136189 q = 1) : d139594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136189, d139594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136189, d139594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11912 (p : Pattern) (selected : d136234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6403 q selected
  have h2 (q : Pattern) (selected : d136228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
  have h4 (q : Pattern) (selected : d136230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11913 (p : Pattern) (selected : d136238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
  have h2 (q : Pattern) (selected : d136230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136237 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136238 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11914 (p : Pattern) (selected : d136244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11912 q selected
    | true =>
      simp only [d136235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11913 q selected
    | true =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136241 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136242 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136243 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11915 (p : Pattern) (selected : d136248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11913 q selected
    | true =>
      simp only [d136239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136245 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136246 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136247 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11916 (p : Pattern) (selected : d136267 p = 1) : d139604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136226 q = 1) : d136226 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11914 q selected
    | true =>
      simp only [d136249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11915 q selected
  have h3 (q : Pattern) (selected : d136250 q = 1) : d139600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136250, d139600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136250, d139600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136263 q = 1) : d136263 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136264 q = 1) : d139601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136264, d139601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136264, d139601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136265 q = 1) : d139602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136265, d139602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136265, d139602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136266 q = 1) : d139603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136266, d139603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136266, d139603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136267 q = 1) : d139604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136267, d139604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136267, d139604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11917 (p : Pattern) (selected : d136284 p = 1) : d139610 p = 1 := by
  have h0 (q : Pattern) (selected : d136075 q = 1) : d136075 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136170 q = 1) : d139588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136170, d139588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11907 q selected
    | true =>
      simp only [d136170, d139588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11910 q selected
  have h2 (q : Pattern) (selected : d136183 q = 1) : d136183 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136184 q = 1) : d139589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136184, d139589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136184, d139589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136185 q = 1) : d139590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136185, d139590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136185, d139590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136186 q = 1) : d139591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136186, d139591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136186, d139591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136190 q = 1) : d139595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136190, d139595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136190, d139595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11911 q selected
  have h8 (q : Pattern) (selected : d136192 q = 1) : d136192 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d136193 q = 1) : d139596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136193, d139596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136193, d139596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136194 q = 1) : d139597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136194, d139597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136194, d139597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d136195 q = 1) : d139598 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136195, d139598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136195, d139598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d136196 q = 1) : d139599 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136196, d139599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136196, d139599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136268 q = 1) : d139605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136268, d139605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136268, d139605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11916 q selected
  have h14 (q : Pattern) (selected : d136279 q = 1) : d136279 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136280 q = 1) : d139606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136280, d139606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136280, d139606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136281 q = 1) : d139607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136281, d139607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136281, d139607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d136282 q = 1) : d139608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136282, d139608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136282, d139608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d136283 q = 1) : d139609 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136283, d139609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136283, d139609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d136284 q = 1) : d139610 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136284, d139610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d136284, d139610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11918 (p : Pattern) (selected : d136290 p = 1) : d139616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136285 q = 1) : d139611 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136285, d139611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136285, d139611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11917 q selected
  have h2 (q : Pattern) (selected : d136286 q = 1) : d139612 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136286, d139612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136286, d139612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136287 q = 1) : d139613 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136287, d139613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136287, d139613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136288 q = 1) : d139614 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136288, d139614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136288, d139614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136289 q = 1) : d139615 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136289, d139615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136289, d139615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136290 q = 1) : d139616 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136290, d139616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136290, d139616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11919 (p : Pattern) (selected : d136371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6413 q selected
  have h2 (q : Pattern) (selected : d136365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
  have h4 (q : Pattern) (selected : d136367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11920 (p : Pattern) (selected : d136375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
  have h2 (q : Pattern) (selected : d136367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136374 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136375 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11921 (p : Pattern) (selected : d136381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11919 q selected
    | true =>
      simp only [d136372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11922 (p : Pattern) (selected : d136385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11923 (p : Pattern) (selected : d136404 p = 1) : d139624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136342 q = 1) : d136342 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136351 q = 1) : d136351 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136363 q = 1) : d136363 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d136386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11921 q selected
    | true =>
      simp only [d136386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11922 q selected
  have h5 (q : Pattern) (selected : d136387 q = 1) : d139620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136387, d139620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136387, d139620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136400 q = 1) : d136400 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d136401 q = 1) : d139621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136401, d139621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136401, d139621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136402 q = 1) : d139622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136402, d139622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136402, d139622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136403 q = 1) : d139623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136403, d139623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136403, d139623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136404 q = 1) : d139624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136404, d139624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136404, d139624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11924 (p : Pattern) (selected : d136418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11919 q selected
    | true =>
      simp only [d136372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136418 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11925 (p : Pattern) (selected : d136419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11920 q selected
    | true =>
      simp only [d136376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11926 (p : Pattern) (selected : d136428 p = 1) : d139629 p = 1 := by
  have h0 (q : Pattern) (selected : d136342 q = 1) : d136342 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136351 q = 1) : d136351 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136363 q = 1) : d136363 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11921 q selected
    | true =>
      simp only [d136386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11922 q selected
  have h4 (q : Pattern) (selected : d136387 q = 1) : d139620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136387, d139620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136387, d139620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136400 q = 1) : d136400 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d136401 q = 1) : d139621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136401, d139621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136401, d139621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136402 q = 1) : d139622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136402, d139622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136402, d139622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136403 q = 1) : d139623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136403, d139623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136403, d139623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136410 q = 1) : d136410 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d136415 q = 1) : d136415 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d136417 q = 1) : d136417 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d136420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11924 q selected
    | true =>
      simp only [d136420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11925 q selected
  have h13 (q : Pattern) (selected : d136421 q = 1) : d139625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136421, d139625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136421, d139625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136424 q = 1) : d136424 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136425 q = 1) : d139626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136425, d139626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136425, d139626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136426 q = 1) : d139627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136426, d139627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136426, d139627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136427 q = 1) : d139628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136427, d139628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136427, d139628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136428 q = 1) : d139629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136428, d139629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136428, d139629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11927 (p : Pattern) (selected : d136448 p = 1) : d139636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136417 q = 1) : d136417 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11924 q selected
    | true =>
      simp only [d136420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11925 q selected
  have h3 (q : Pattern) (selected : d136421 q = 1) : d139625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136421, d139625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136421, d139625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136424 q = 1) : d136424 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136425 q = 1) : d139626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136425, d139626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136425, d139626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136446 q = 1) : d139634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136446, d139634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136446, d139634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136447 q = 1) : d139635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136447, d139635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136447, d139635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136448 q = 1) : d139636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136448, d139636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136448, d139636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11928 (p : Pattern) (selected : d136493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6425 q selected
  have h2 (q : Pattern) (selected : d136487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136488 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
  have h4 (q : Pattern) (selected : d136489 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136490 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136491 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136492 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136493 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11929 (p : Pattern) (selected : d136497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136488 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
  have h2 (q : Pattern) (selected : d136489 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136491 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136496 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136497 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11930 (p : Pattern) (selected : d136503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136494 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11928 q selected
    | true =>
      simp only [d136494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136495 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136498 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11929 q selected
    | true =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136499 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136500 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136501 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136502 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136503 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11931 (p : Pattern) (selected : d136507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136498 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11929 q selected
    | true =>
      simp only [d136498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136499 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136504 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11932 (p : Pattern) (selected : d136526 p = 1) : d139646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136485 q = 1) : d136485 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11930 q selected
    | true =>
      simp only [d136508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11931 q selected
  have h3 (q : Pattern) (selected : d136509 q = 1) : d139642 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136509, d139642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136509, d139642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136522 q = 1) : d136522 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136523 q = 1) : d139643 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136523, d139643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136523, d139643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136524 q = 1) : d139644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136524, d139644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136524, d139644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136525 q = 1) : d139645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136525, d139645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136525, d139645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136526 q = 1) : d139646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136526, d139646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136526, d139646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11933 (p : Pattern) (selected : d136543 p = 1) : d139652 p = 1 := by
  have h0 (q : Pattern) (selected : d136334 q = 1) : d136334 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136429 q = 1) : d139630 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136429, d139630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11923 q selected
    | true =>
      simp only [d136429, d139630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11926 q selected
  have h2 (q : Pattern) (selected : d136442 q = 1) : d136442 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136443 q = 1) : d139631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136443, d139631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136443, d139631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136444 q = 1) : d139632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136444, d139632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136444, d139632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136445 q = 1) : d139633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136445, d139633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136445, d139633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136449 q = 1) : d139637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136449, d139637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136449, d139637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11927 q selected
  have h8 (q : Pattern) (selected : d136451 q = 1) : d136451 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d136452 q = 1) : d139638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136452, d139638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136452, d139638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136453 q = 1) : d139639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136453, d139639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136453, d139639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d136454 q = 1) : d139640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136454, d139640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136454, d139640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d136455 q = 1) : d139641 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136455, d139641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136455, d139641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136527 q = 1) : d139647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136527, d139647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136527, d139647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11932 q selected
  have h14 (q : Pattern) (selected : d136538 q = 1) : d136538 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136539 q = 1) : d139648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136539, d139648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136539, d139648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136540 q = 1) : d139649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136540, d139649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136540, d139649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d136541 q = 1) : d139650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136541, d139650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136541, d139650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d136542 q = 1) : d139651 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136542, d139651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136542, d139651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d136543 q = 1) : d139652 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136543, d139652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d136543, d139652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11934 (p : Pattern) (selected : d136549 p = 1) : d139658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136544 q = 1) : d139653 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136544, d139653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136544, d139653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11933 q selected
  have h2 (q : Pattern) (selected : d136545 q = 1) : d139654 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136545, d139654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136545, d139654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136546 q = 1) : d139655 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136546, d139655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136546, d139655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136547 q = 1) : d139656 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136547, d139656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136547, d139656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136548 q = 1) : d139657 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136548, d139657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136548, d139657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136549 q = 1) : d139658 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136549, d139658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136549, d139658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11935 (p : Pattern) (selected : d136631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136624 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6435 q selected
  have h2 (q : Pattern) (selected : d136625 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136626 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
  have h4 (q : Pattern) (selected : d136627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136628 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136630 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11936 (p : Pattern) (selected : d136635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136626 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
  have h2 (q : Pattern) (selected : d136627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136634 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136635 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11937 (p : Pattern) (selected : d136641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11935 q selected
    | true =>
      simp only [d136632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11938 (p : Pattern) (selected : d136645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136642 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136643 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136644 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136645 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11939 (p : Pattern) (selected : d136664 p = 1) : d139667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136602 q = 1) : d136602 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136611 q = 1) : d136611 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136623 q = 1) : d136623 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d136646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11937 q selected
    | true =>
      simp only [d136646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11938 q selected
  have h5 (q : Pattern) (selected : d136647 q = 1) : d139663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136647, d139663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136647, d139663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136660 q = 1) : d136660 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d136661 q = 1) : d139664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136661, d139664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136661, d139664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136662 q = 1) : d139665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136662, d139665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136662, d139665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136663 q = 1) : d139666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136663, d139666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136663, d139666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136664 q = 1) : d139667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136664, d139667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136664, d139667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11940 (p : Pattern) (selected : d136678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11935 q selected
    | true =>
      simp only [d136632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11941 (p : Pattern) (selected : d136679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11936 q selected
    | true =>
      simp only [d136636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136642 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136643 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136644 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11942 (p : Pattern) (selected : d136688 p = 1) : d139672 p = 1 := by
  have h0 (q : Pattern) (selected : d136602 q = 1) : d136602 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136611 q = 1) : d136611 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136623 q = 1) : d136623 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136646 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11937 q selected
    | true =>
      simp only [d136646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11938 q selected
  have h4 (q : Pattern) (selected : d136647 q = 1) : d139663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136647, d139663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136647, d139663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136660 q = 1) : d136660 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d136661 q = 1) : d139664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136661, d139664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136661, d139664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136662 q = 1) : d139665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136662, d139665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136662, d139665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136663 q = 1) : d139666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136663, d139666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136663, d139666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136670 q = 1) : d136670 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d136675 q = 1) : d136675 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d136677 q = 1) : d136677 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d136680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11940 q selected
    | true =>
      simp only [d136680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11941 q selected
  have h13 (q : Pattern) (selected : d136681 q = 1) : d139668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136681, d139668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d136681, d139668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136684 q = 1) : d136684 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136685 q = 1) : d139669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136685, d139669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136685, d139669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136686 q = 1) : d139670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136686, d139670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136686, d139670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d136687 q = 1) : d139671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136687, d139671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136687, d139671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d136688 q = 1) : d139672 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136688, d139672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d136688, d139672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro11943 (p : Pattern) (selected : d136708 p = 1) : d139679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136677 q = 1) : d136677 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136680 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11940 q selected
    | true =>
      simp only [d136680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11941 q selected
  have h3 (q : Pattern) (selected : d136681 q = 1) : d139668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136681, d139668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136681, d139668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136684 q = 1) : d136684 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136685 q = 1) : d139669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136685, d139669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136685, d139669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136706 q = 1) : d139677 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136706, d139677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136706, d139677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136707 q = 1) : d139678 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136707, d139678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136707, d139678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136708 q = 1) : d139679 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136708, d139679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136708, d139679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11944 (p : Pattern) (selected : d136753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6447 q selected
  have h2 (q : Pattern) (selected : d136747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
  have h4 (q : Pattern) (selected : d136749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136752 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11945 (p : Pattern) (selected : d136757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
  have h2 (q : Pattern) (selected : d136749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136756 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136757 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11946 (p : Pattern) (selected : d136763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11944 q selected
    | true =>
      simp only [d136754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136758 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11945 q selected
    | true =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136759 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136760 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136761 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d136762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d136763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11947 (p : Pattern) (selected : d136767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136758 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11945 q selected
    | true =>
      simp only [d136758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136759 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11948 (p : Pattern) (selected : d136786 p = 1) : d139689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136745 q = 1) : d136745 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11946 q selected
    | true =>
      simp only [d136768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11947 q selected
  have h3 (q : Pattern) (selected : d136769 q = 1) : d139685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136769, d139685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136769, d139685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136782 q = 1) : d136782 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136783 q = 1) : d139686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136783, d139686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136783, d139686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136784 q = 1) : d139687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136784, d139687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136784, d139687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136785 q = 1) : d139688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136785, d139688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136785, d139688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d136786 q = 1) : d139689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136786, d139689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136786, d139689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11949 (p : Pattern) (selected : d136803 p = 1) : d139695 p = 1 := by
  have h0 (q : Pattern) (selected : d136594 q = 1) : d136594 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136689 q = 1) : d139673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136689, d139673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11939 q selected
    | true =>
      simp only [d136689, d139673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11942 q selected
  have h2 (q : Pattern) (selected : d136702 q = 1) : d136702 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d136703 q = 1) : d139674 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136703, d139674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136703, d139674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d136704 q = 1) : d139675 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136704, d139675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136704, d139675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136705 q = 1) : d139676 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136705, d139676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136705, d139676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136709 q = 1) : d139680 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136709, d139680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136709, d139680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11943 q selected
  have h8 (q : Pattern) (selected : d136711 q = 1) : d136711 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d136712 q = 1) : d139681 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136712, d139681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d136712, d139681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136713 q = 1) : d139682 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136713, d139682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d136713, d139682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d136714 q = 1) : d139683 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136714, d139683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136714, d139683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d136715 q = 1) : d139684 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136715, d139684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136715, d139684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136787 q = 1) : d139690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136787, d139690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136787, d139690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11948 q selected
  have h14 (q : Pattern) (selected : d136798 q = 1) : d136798 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d136799 q = 1) : d139691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136799, d139691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d136799, d139691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136800 q = 1) : d139692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136800, d139692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136800, d139692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d136801 q = 1) : d139693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136801, d139693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d136801, d139693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d136802 q = 1) : d139694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136802, d139694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d136802, d139694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d136803 q = 1) : d139695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d136803, d139695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d136803, d139695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11950 (p : Pattern) (selected : d136809 p = 1) : d139701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136804 q = 1) : d139696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d136804, d139696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136804, d139696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11949 q selected
  have h2 (q : Pattern) (selected : d136805 q = 1) : d139697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d136805, d139697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136805, d139697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d136806 q = 1) : d139698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d136806, d139698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136806, d139698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136807 q = 1) : d139699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d136807, d139699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136807, d139699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d136808 q = 1) : d139700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d136808, d139700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136808, d139700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136809 q = 1) : d139701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d136809, d139701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136809, d139701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11951 (p : Pattern) (selected : d136815 p = 1) : d139707 p = 1 := by
  have h0 (q : Pattern) (selected : d135776 q = 1) : d139536 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d135776, d139536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11875 q selected
    | true =>
      simp only [d135776, d139536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11886 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d136033 q = 1) : d139576 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136033, d139576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136033, d139576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11902 q selected
  have h3 (q : Pattern) (selected : d136034 q = 1) : d139577 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136034, d139577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d136034, d139577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d136291 q = 1) : d139617 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136291, d139617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136291, d139617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11918 q selected
  have h5 (q : Pattern) (selected : d136292 q = 1) : d139618 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136292, d139618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136292, d139618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d136293 q = 1) : d139619 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136293, d139619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136293, d139619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d136550 q = 1) : d139659 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136550, d139659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136550, d139659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11934 q selected
  have h8 (q : Pattern) (selected : d136551 q = 1) : d139660 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136551, d139660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136551, d139660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d136552 q = 1) : d139661 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136552, d139661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136552, d139661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d136553 q = 1) : d139662 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d136553, d139662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d136553, d139662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d136810 q = 1) : d139702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d136810, d139702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136810, d139702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11950 q selected
  have h12 (q : Pattern) (selected : d136811 q = 1) : d139703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d136811, d139703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136811, d139703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d136812 q = 1) : d139704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d136812, d139704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136812, d139704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d136813 q = 1) : d139705 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d136813, d139705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136813, d139705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d136814 q = 1) : d139706 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d136814, d139706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d136814, d139706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d136815 q = 1) : d139707 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d136815, d139707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d136815, d139707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro11952 (p : Pattern) (selected : d136821 p = 1) : d139713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136816 q = 1) : d139708 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d136816, d139708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11951 q selected
    | true =>
      simp only [d136816, d139708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136817 q = 1) : d139709 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d136817, d139709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136817, d139709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136818 q = 1) : d139710 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d136818, d139710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136818, d139710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136819 q = 1) : d139711 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d136819, d139711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136819, d139711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136820 q = 1) : d139712 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d136820, d139712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136820, d139712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136821 q = 1) : d139713 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d136821, d139713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136821, d139713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11953 (p : Pattern) (selected : d136827 p = 1) : d139719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136822 q = 1) : d139714 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d136822, d139714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11952 q selected
    | true =>
      simp only [d136822, d139714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136823 q = 1) : d139715 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d136823, d139715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136823, d139715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136824 q = 1) : d139716 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d136824, d139716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136824, d139716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136825 q = 1) : d139717 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d136825, d139717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136825, d139717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136826 q = 1) : d139718 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d136826, d139718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136826, d139718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136827 q = 1) : d139719 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d136827, d139719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136827, d139719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11954 (p : Pattern) (selected : d136833 p = 1) : d139725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136828 q = 1) : d139720 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d136828, d139720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11953 q selected
    | true =>
      simp only [d136828, d139720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136829 q = 1) : d139721 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d136829, d139721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136829, d139721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136830 q = 1) : d139722 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d136830, d139722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136830, d139722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136831 q = 1) : d139723 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d136831, d139723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136831, d139723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136832 q = 1) : d139724 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d136832, d139724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136832, d139724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136833 q = 1) : d139725 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d136833, d139725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136833, d139725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11955 (p : Pattern) (selected : d136839 p = 1) : d139731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136834 q = 1) : d139726 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d136834, d139726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11954 q selected
    | true =>
      simp only [d136834, d139726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136835 q = 1) : d139727 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d136835, d139727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136835, d139727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136836 q = 1) : d139728 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d136836, d139728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136836, d139728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136837 q = 1) : d139729 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d136837, d139729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136837, d139729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136838 q = 1) : d139730 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d136838, d139730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136838, d139730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136839 q = 1) : d139731 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d136839, d139731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136839, d139731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11956 (p : Pattern) (selected : d136845 p = 1) : d139737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136840 q = 1) : d139732 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d136840, d139732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11955 q selected
    | true =>
      simp only [d136840, d139732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136841 q = 1) : d139733 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d136841, d139733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136841, d139733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136842 q = 1) : d139734 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d136842, d139734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136842, d139734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136843 q = 1) : d139735 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d136843, d139735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136843, d139735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136844 q = 1) : d139736 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d136844, d139736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136844, d139736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136845 q = 1) : d139737 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d136845, d139737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136845, d139737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11957 (p : Pattern) (selected : d136851 p = 1) : d139743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136846 q = 1) : d139738 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d136846, d139738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11956 q selected
    | true =>
      simp only [d136846, d139738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136847 q = 1) : d139739 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d136847, d139739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136847, d139739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136848 q = 1) : d139740 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d136848, d139740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136848, d139740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136849 q = 1) : d139741 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d136849, d139741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136849, d139741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136850 q = 1) : d139742 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d136850, d139742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136850, d139742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136851 q = 1) : d139743 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d136851, d139743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136851, d139743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11958 (p : Pattern) (selected : d136857 p = 1) : d139749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d136852 q = 1) : d139744 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d136852, d139744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11957 q selected
    | true =>
      simp only [d136852, d139744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d136853 q = 1) : d139745 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d136853, d139745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d136853, d139745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d136854 q = 1) : d139746 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d136854, d139746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d136854, d139746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d136855 q = 1) : d139747 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d136855, d139747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d136855, d139747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d136856 q = 1) : d139748 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d136856, d139748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d136856, d139748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d136857 q = 1) : d139749 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d136857, d139749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d136857, d139749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11959 (p : Pattern) (selected : d10654 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10652 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d34 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10653 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10654 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11960 (p : Pattern) (selected : d10660 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10659 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10660 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11961 (p : Pattern) (selected : d10666 p = 2) : d104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
    | true =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10662 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10662, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10663 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10663, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10664 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10664, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10665 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10665, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10666 q = 2) : d104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10666, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10666, d104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11962 (p : Pattern) (selected : d10667 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10659 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10667 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11963 (p : Pattern) (selected : d10673 p = 2) : d111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
    | true =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10662 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10662, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10663 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10663, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10664 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10664, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10665 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10665, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10668 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11962 q selected
    | true =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h24 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d10669 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10669, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10670 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10670, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10671 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10671, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10671, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10672 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10672, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10672, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d10673 q = 2) : d111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10673, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10673, d111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11964 (p : Pattern) (selected : d10680 p = 2) : d406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10668 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11962 q selected
    | true =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h2 (q : Pattern) (selected : d206 q = 2) : d50 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
    | true =>
      simp only [d206, d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10669 q = 2) : d107 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10669, d107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10670 q = 2) : d108 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10670, d108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10678 q = 2) : d109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10678, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10678, d109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10679 q = 2) : d110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10679, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10679, d110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10680 q = 2) : d406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10680, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10680, d406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11965 (p : Pattern) (selected : d10691 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10686 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
    | true =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10687 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10688 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10689 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d75 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10690 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10691 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11966 (p : Pattern) (selected : d10697 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10692 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11965 q selected
    | true =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10693 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro654 q selected
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10694 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10695 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10696 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10697 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11967 (p : Pattern) (selected : d10703 p = 2) : d462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10698 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11966 q selected
    | true =>
      simp only [d10698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro655 q selected
  have h2 (q : Pattern) (selected : d263 q = 2) : d84 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro685 q selected
    | true =>
      simp only [d263, d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10699 q = 2) : d458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10699, d458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10699, d458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro655 q selected
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10700 q = 2) : d459 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10700, d459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10700, d459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10701 q = 2) : d460 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10701, d460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10701, d460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10702 q = 2) : d461 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10702, d461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10702, d461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10703 q = 2) : d462 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10703, d462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10703, d462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11968 (p : Pattern) (selected : d10709 p = 2) : d53647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d105 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
  have h2 (q : Pattern) (selected : d106 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h4 (q : Pattern) (selected : d113 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10674 q = 2) : d112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10674, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11961 q selected
    | true =>
      simp only [d10674, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11963 q selected
  have h7 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10675 q = 2) : d113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10675, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10675, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10676 q = 2) : d53637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10676, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10676, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10677 q = 2) : d53638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10677, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10677, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10681 q = 2) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10681, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10681, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11964 q selected
  have h12 (q : Pattern) (selected : d10682 q = 2) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10682, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10682, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10683 q = 2) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10683, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10683, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10684 q = 2) : d53641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10684, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10684, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10685 q = 2) : d53642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10685, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10685, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10704 q = 2) : d463 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10704, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10704, d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11967 q selected
  have h17 (q : Pattern) (selected : d10705 q = 2) : d53643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10705, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10705, d53643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10706 q = 2) : d53644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10706, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10706, d53644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10707 q = 2) : d53645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10707, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10707, d53645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d10708 q = 2) : d53646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10708, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10708, d53646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10709 q = 2) : d53647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10709, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10709, d53647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro11969 (p : Pattern) (selected : d10719 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
    | true =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d10715 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10719 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11970 (p : Pattern) (selected : d10726 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
    | true =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d10715 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10668 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11962 q selected
    | true =>
      simp only [d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro650 q selected
  have h7 (q : Pattern) (selected : d10722 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10723 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10724 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10725 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10726 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11971 (p : Pattern) (selected : d10731 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10730 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10731 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11972 (p : Pattern) (selected : d10738 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10736 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10737 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10738 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11973 (p : Pattern) (selected : d10747 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10742 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro694 q selected
    | true =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10743 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10744 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10745 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10652 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10746 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10747 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro11974 (p : Pattern) (selected : d10753 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10748 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11973 q selected
    | true =>
      simp only [d10748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10749 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10750 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10751 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10752 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10753 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11975 (p : Pattern) (selected : d10760 p = 2) : d10654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10755 q = 2) : d10649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d10755, d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10756 q = 2) : d10650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10757 q = 2) : d10651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 2) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
    | true =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 2) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d32, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 2) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d33, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10758 q = 2) : d10652 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10758, d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10758, d10652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 2) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, d34, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10759 q = 2) : d10653 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10759, d10653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10759, d10653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10760 q = 2) : d10654 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10760, d10654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10760, d10654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11976 (p : Pattern) (selected : d10766 p = 2) : d10660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10761 q = 2) : d10655 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11975 q selected
    | true =>
      simp only [d10761, d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 2) : d10656 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 2) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro670 q selected
    | true =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 2) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 2) : d10657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 2) : d10658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 2) : d10659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10766 q = 2) : d10660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10766, d10660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10766, d10660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11977 (p : Pattern) (selected : d10772 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10769 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10770 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10771 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10772 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11978 (p : Pattern) (selected : d10778 p = 2) : d10719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10732 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11971 q selected
    | true =>
      simp only [d10732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d10733 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10734 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10735 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10739 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11972 q selected
    | true =>
      simp only [d10739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d10740 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10741 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10754 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11974 q selected
    | true =>
      simp only [d10754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
  have h9 (q : Pattern) (selected : d10767 q = 2) : d10661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11976 q selected
    | true =>
      simp only [d10767, d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d10768 q = 2) : d10715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10768, d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10773 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11977 q selected
    | true =>
      simp only [d10773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10774 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10775 q = 2) : d10716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10775, d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10776 q = 2) : d10717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10776, d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10777 q = 2) : d10718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10777, d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10778 q = 2) : d10719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10778, d10719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10778, d10719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11979 (p : Pattern) (selected : d10779 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10730 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10779 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11980 (p : Pattern) (selected : d10784 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro647 q selected
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10736 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10737 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10784 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11981 (p : Pattern) (selected : d10788 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10748 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11973 q selected
    | true =>
      simp only [d10748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10749 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10750 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10751 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10752 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10788 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11982 (p : Pattern) (selected : d10790 p = 2) : d10667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10761 q = 2) : d10655 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11975 q selected
    | true =>
      simp only [d10761, d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 2) : d10656 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 2) : d37 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro670 q selected
    | true =>
      simp only [d182, d37, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 2) : d38 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d38, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 2) : d10657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, d10657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 2) : d10658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, d10658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 2) : d10659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, d10659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10790 q = 2) : d10667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10790, d10667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10790, d10667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11983 (p : Pattern) (selected : d10793 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10655 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11959 q selected
    | true =>
      simp only [d10655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10769 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10770 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10771 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10793 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11984 (p : Pattern) (selected : d10799 p = 2) : d10726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10732 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11971 q selected
    | true =>
      simp only [d10732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d10733 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10734 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10735 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10739 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11972 q selected
    | true =>
      simp only [d10739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d10740 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10741 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10754 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11974 q selected
    | true =>
      simp only [d10754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
  have h9 (q : Pattern) (selected : d10767 q = 2) : d10661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11976 q selected
    | true =>
      simp only [d10767, d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d10768 q = 2) : d10715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10768, d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10773 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11977 q selected
    | true =>
      simp only [d10773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10774 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10775 q = 2) : d10716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10775, d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10776 q = 2) : d10717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10776, d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10777 q = 2) : d10718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10777, d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10780 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11979 q selected
    | true =>
      simp only [d10780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
  have h17 (q : Pattern) (selected : d10781 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10782 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10783 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10785 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11980 q selected
    | true =>
      simp only [d10785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro674 q selected
  have h21 (q : Pattern) (selected : d10786 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d10787 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d10787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10789 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11981 q selected
    | true =>
      simp only [d10789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11962 q selected
  have h24 (q : Pattern) (selected : d10791 q = 2) : d10668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11982 q selected
    | true =>
      simp only [d10791, d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h25 (q : Pattern) (selected : d10792 q = 2) : d10722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10792, d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10794 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11983 q selected
    | true =>
      simp only [d10794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d10795 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d10795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10796 q = 2) : d10723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10796, d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10797 q = 2) : d10724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10797, d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10797, d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10798 q = 2) : d10725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10798, d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10798, d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d10799 q = 2) : d10726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10799, d10726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10799, d10726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11985 (p : Pattern) (selected : d10801 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10661 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11960 q selected
    | true =>
      simp only [d10661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h2 (q : Pattern) (selected : d10715 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10801 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11986 (p : Pattern) (selected : d10808 p = 2) : d109112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10789 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11981 q selected
    | true =>
      simp only [d10789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11962 q selected
  have h2 (q : Pattern) (selected : d10791 q = 2) : d10668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11982 q selected
    | true =>
      simp only [d10791, d10668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro676 q selected
  have h3 (q : Pattern) (selected : d10792 q = 2) : d10722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10792, d10722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10794 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11983 q selected
    | true =>
      simp only [d10794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10795 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10796 q = 2) : d10723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10796, d10723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10806 q = 2) : d10724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10806, d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10806, d10724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10807 q = 2) : d10725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10807, d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10807, d10725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10808 q = 2) : d109112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10808, d109112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10808, d109112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11987 (p : Pattern) (selected : d10819 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10814 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro711 q selected
    | true =>
      simp only [d10814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10815 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10816 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10686 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro680 q selected
    | true =>
      simp only [d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10687 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10688 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10817 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro653 q selected
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d73 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d74 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10689 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10818 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10819 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro11988 (p : Pattern) (selected : d10825 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10820 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11987 q selected
    | true =>
      simp only [d10820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10821 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10692 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11965 q selected
    | true =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10693 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10822 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10823 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10824 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10825 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11989 (p : Pattern) (selected : d10832 p = 2) : d10691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10827 q = 2) : d10686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro714 q selected
    | true =>
      simp only [d10827, d10686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10828 q = 2) : d10687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, d10687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10829 q = 2) : d10688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, d10688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 2) : d72 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro683 q selected
    | true =>
      simp only [d251, d72, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 2) : d73 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d73, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 2) : d74 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d74, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10830 q = 2) : d10689 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10830, d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10830, d10689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 2) : d75 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, d75, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, d75, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10831 q = 2) : d10690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10831, d10690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10831, d10690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10832 q = 2) : d10691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10832, d10691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10832, d10691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11990 (p : Pattern) (selected : d10838 p = 2) : d10697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10833 q = 2) : d10692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10833, d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11989 q selected
    | true =>
      simp only [d10833, d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10834 q = 2) : d10693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10834, d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10834, d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 2) : d78 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro684 q selected
    | true =>
      simp only [d257, d78, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 2) : d79 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d79, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10835 q = 2) : d10694 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10835, d10694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10835, d10694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10836 q = 2) : d10695 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10836, d10695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10836, d10695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10837 q = 2) : d10696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10837, d10696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10837, d10696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10838 q = 2) : d10697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10838, d10697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10838, d10697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11991 (p : Pattern) (selected : d10844 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10692 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11965 q selected
    | true =>
      simp only [d10692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10693 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10841 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10842 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10843 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10844 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11992 (p : Pattern) (selected : d10850 p = 2) : d109122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10826 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11988 q selected
    | true =>
      simp only [d10826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11966 q selected
  have h2 (q : Pattern) (selected : d10839 q = 2) : d10698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10839, d10698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11990 q selected
    | true =>
      simp only [d10839, d10698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro685 q selected
  have h3 (q : Pattern) (selected : d10840 q = 2) : d109118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10840, d109118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10840, d109118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10845 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11991 q selected
    | true =>
      simp only [d10845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10846 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10847 q = 2) : d109119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10847, d109119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10847, d109119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10848 q = 2) : d109120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10848, d109120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10848, d109120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10849 q = 2) : d109121 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10849, d109121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10849, d109121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10850 q = 2) : d109122 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10850, d109122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10850, d109122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11993 (p : Pattern) (selected : d10856 p = 2) : d109128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10720 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11969 q selected
  have h2 (q : Pattern) (selected : d10721 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10727 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11969 q selected
    | true =>
      simp only [d10727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11970 q selected
  have h4 (q : Pattern) (selected : d10728 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10729 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10800 q = 2) : d10727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10800, d10727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11978 q selected
    | true =>
      simp only [d10800, d10727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11984 q selected
  have h7 (q : Pattern) (selected : d10802 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11985 q selected
    | true =>
      simp only [d10802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h8 (q : Pattern) (selected : d10803 q = 2) : d10728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10803, d10728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10803, d10728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10804 q = 2) : d109110 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10804, d109110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10804, d109110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10805 q = 2) : d109111 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10805, d109111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10805, d109111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10809 q = 2) : d109113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10809, d109113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10809, d109113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11986 q selected
  have h12 (q : Pattern) (selected : d407 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro710 q selected
  have h13 (q : Pattern) (selected : d10810 q = 2) : d109114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10810, d109114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10810, d109114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10811 q = 2) : d109115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10811, d109115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10811, d109115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10812 q = 2) : d109116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10812, d109116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10812, d109116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10813 q = 2) : d109117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10813, d109117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10813, d109117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10851 q = 2) : d109123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10851, d109123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10851, d109123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11992 q selected
  have h18 (q : Pattern) (selected : d463 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro718 q selected
  have h19 (q : Pattern) (selected : d10852 q = 2) : d109124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10852, d109124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10852, d109124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10853 q = 2) : d109125 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10853, d109125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10853, d109125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10854 q = 2) : d109126 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10854, d109126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10854, d109126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10855 q = 2) : d109127 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10855, d109127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d10855, d109127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10856 q = 2) : d109128 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10856, d109128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10856, d109128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11994 (p : Pattern) (selected : d10862 p = 2) : d109134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d96 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro657 q selected
  have h2 (q : Pattern) (selected : d97 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10710 q = 2) : d53648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10710, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10710, d53648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11968 q selected
  have h6 (q : Pattern) (selected : d10711 q = 2) : d53649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10711, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10711, d53649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10712 q = 2) : d53650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10712, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10712, d53650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10713 q = 2) : d53651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10713, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10713, d53651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10714 q = 2) : d53652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10714, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10714, d53652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10857 q = 2) : d109129 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10857, d109129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10857, d109129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11993 q selected
  have h11 (q : Pattern) (selected : d10858 q = 2) : d109130 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10858, d109130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10858, d109130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10859 q = 2) : d109131 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10859, d109131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10859, d109131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10860 q = 2) : d109132 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10860, d109132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10860, d109132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10861 q = 2) : d109133 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10861, d109133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10861, d109133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10862 q = 2) : d109134 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d10862, d109134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10862, d109134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro11995 (p : Pattern) (selected : d10865 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10742 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro694 q selected
    | true =>
      simp only [d10742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10743 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10744 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10745 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10863 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10864 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10865 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11996 (p : Pattern) (selected : d10869 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d10649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10863 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10868 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10869 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11997 (p : Pattern) (selected : d10875 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10866 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11995 q selected
    | true =>
      simp only [d10866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11996 q selected
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10873 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10874 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10875 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11998 (p : Pattern) (selected : d10879 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10870 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11996 q selected
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10877 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10878 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10879 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11999 (p : Pattern) (selected : d10885 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10880 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11997 q selected
    | true =>
      simp only [d10880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11998 q selected
  have h2 (q : Pattern) (selected : d10881 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10882 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10883 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10884 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10885 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
