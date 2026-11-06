import NetHack.Soko22Hazard87.AndIntroBlocks0363
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro91000 (p : Pattern) (ha : d307565 p = 1) (hb : d332753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307550 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307550, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90995 q ha hb
    | true =>
      simp only [d307550, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90997 q ha hb
  have h2 (q : Pattern) (ha : d307551 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307551, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307551, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307552 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307552, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307552, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307555 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90997 q ha hb
    | true =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90998 q ha hb
  have h5 (q : Pattern) (ha : d307556 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307557 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307558 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307558, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307558, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307563 q = 1) (hb : d332751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307563, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307563, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307564 q = 1) (hb : d332752 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307564, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307564, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307565 q = 1) (hb : d332753 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307565, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307565, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro91001 (p : Pattern) (ha : d307571 p = 1) (hb : d332759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307561 q = 1) (hb : d332749 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307561, d332749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90999 q ha hb
    | true =>
      simp only [d307561, d332749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307562 q = 1) (hb : d332750 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307562, d332750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307562, d332750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307566 q = 1) (hb : d332754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307566, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91000 q ha hb
    | true =>
      simp only [d307566, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307567 q = 1) (hb : d332755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307567, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307567, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307568 q = 1) (hb : d332756 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307568, d332756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307568, d332756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307569 q = 1) (hb : d332757 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307569, d332757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307569, d332757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307570 q = 1) (hb : d332758 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307570, d332758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307570, d332758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307571 q = 1) (hb : d332759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307571, d332759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307571, d332759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91002 (p : Pattern) (ha : d307573 p = 1) (hb : d332761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307555 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90997 q ha hb
    | true =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90998 q ha hb
  have h2 (q : Pattern) (ha : d307556 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307557 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307563 q = 1) (hb : d332751 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307563, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307563, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307572 q = 1) (hb : d332760 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307572, d332760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307572, d332760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307573 q = 1) (hb : d332761 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307573, d332761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307573, d332761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91003 (p : Pattern) (ha : d307579 p = 1) (hb : d332767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307566 q = 1) (hb : d332754 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307566, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91000 q ha hb
    | true =>
      simp only [d307566, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307567 q = 1) (hb : d332755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307567, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307567, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307574 q = 1) (hb : d332762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307574, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91002 q ha hb
    | true =>
      simp only [d307574, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307575 q = 1) (hb : d332763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307575, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307575, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307576 q = 1) (hb : d332764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307576, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307576, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307577 q = 1) (hb : d332765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307577, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307577, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307578 q = 1) (hb : d332766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307578, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307578, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307579 q = 1) (hb : d332767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307579, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307579, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91004 (p : Pattern) (ha : d307592 p = 1) (hb : d332775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307540 q = 1) (hb : d332728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307540, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307540, d332728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90954 q ha hb
  have h2 (q : Pattern) (ha : d307286 q = 1) (hb : d332502 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307286, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90954 q ha hb
    | true =>
      simp only [d307286, d332502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307541 q = 1) (hb : d332729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307541, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307541, d332729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307287 q = 1) (hb : d332503 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307287, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307287, d332503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307542 q = 1) (hb : d332730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307542, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307542, d332730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307543 q = 1) (hb : d332731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307543, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307543, d332731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307544 q = 1) (hb : d332732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307544, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307544, d332732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90955 q ha hb
  have h8 (q : Pattern) (ha : d307291 q = 1) (hb : d332507 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307291, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90955 q ha hb
    | true =>
      simp only [d307291, d332507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307545 q = 1) (hb : d332733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307545, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307545, d332733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307292 q = 1) (hb : d332508 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307292, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307292, d332508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307546 q = 1) (hb : d332734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307546, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307546, d332734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307547 q = 1) (hb : d332735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307547, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307547, d332735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307548 q = 1) (hb : d332736 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307548, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307548, d332736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307587 q = 1) (hb : d332770 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307587, d332770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307587, d332770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90976 q ha hb
  have h15 (q : Pattern) (ha : d307413 q = 1) (hb : d332609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307413, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90976 q ha hb
    | true =>
      simp only [d307413, d332609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307588 q = 1) (hb : d332771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307588, d332771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307588, d332771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307414 q = 1) (hb : d332610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307414, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307414, d332610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307589 q = 1) (hb : d332772 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307589, d332772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307589, d332772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307590 q = 1) (hb : d332773 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307590, d332773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307590, d332773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307591 q = 1) (hb : d332774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307591, d332774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307591, d332774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307592 q = 1) (hb : d332775 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307592, d332775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307592, d332775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro91005 (p : Pattern) (ha : d307598 p = 1) (hb : d332781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307593 q = 1) (hb : d332776 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307593, d332776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307593, d332776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90978 q ha hb
  have h2 (q : Pattern) (ha : d307420 q = 1) (hb : d332616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307420, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90978 q ha hb
    | true =>
      simp only [d307420, d332616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307594 q = 1) (hb : d332777 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307594, d332777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307594, d332777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307421 q = 1) (hb : d332617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307421, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307421, d332617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307595 q = 1) (hb : d332778 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307595, d332778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307595, d332778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307596 q = 1) (hb : d332779 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307596, d332779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307596, d332779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307597 q = 1) (hb : d332780 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307597, d332780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307597, d332780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307598 q = 1) (hb : d332781 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307598, d332781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307598, d332781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91006 (p : Pattern) (ha : d307604 p = 1) (hb : d332787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307550 q = 1) (hb : d332738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307550, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90995 q ha hb
    | true =>
      simp only [d307550, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90997 q ha hb
  have h2 (q : Pattern) (ha : d307551 q = 1) (hb : d332739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307551, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307551, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307552 q = 1) (hb : d332740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307552, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307552, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307555 q = 1) (hb : d332743 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90997 q ha hb
    | true =>
      simp only [d307555, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90998 q ha hb
  have h5 (q : Pattern) (ha : d307556 q = 1) (hb : d332744 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307556, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307557 q = 1) (hb : d332745 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307557, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307558 q = 1) (hb : d332746 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307558, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307558, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307599 q = 1) (hb : d332782 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307599, d332782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91004 q ha hb
    | true =>
      simp only [d307599, d332782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91005 q ha hb
  have h9 (q : Pattern) (ha : d307600 q = 1) (hb : d332783 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307600, d332783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307600, d332783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307601 q = 1) (hb : d332784 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307601, d332784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307601, d332784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307602 q = 1) (hb : d332785 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307602, d332785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307602, d332785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307603 q = 1) (hb : d332786 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307603, d332786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307603, d332786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307604 q = 1) (hb : d332787 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307604, d332787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307604, d332787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro91007 (p : Pattern) (ha : d307610 p = 1) (hb : d332793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307605 q = 1) (hb : d332788 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307605, d332788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91006 q ha hb
    | true =>
      simp only [d307605, d332788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307606 q = 1) (hb : d332789 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307606, d332789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307606, d332789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307607 q = 1) (hb : d332790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307607, d332790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307607, d332790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307608 q = 1) (hb : d332791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307608, d332791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307608, d332791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307609 q = 1) (hb : d332792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307609, d332792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307609, d332792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307610 q = 1) (hb : d332793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307610, d332793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307610, d332793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91008 (p : Pattern) (ha : d307616 p = 1) (hb : d332799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307580 q = 1) (hb : d332768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307580, d332768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91001 q ha hb
    | true =>
      simp only [d307580, d332768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91003 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d332769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d332769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307586, d332769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307611 q = 1) (hb : d332794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307611, d332794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91007 q ha hb
    | true =>
      simp only [d307611, d332794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307612 q = 1) (hb : d332795 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307612, d332795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307612, d332795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307613 q = 1) (hb : d332796 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d332796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d332796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307614 q = 1) (hb : d332797 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d332797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d332797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307615 q = 1) (hb : d332798 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d332798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d332798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307616 q = 1) (hb : d332799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d332799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d332799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro91009 (p : Pattern) (ha : d307584 p = 1) (hb : d332804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307574 q = 1) (hb : d332762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307574, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91002 q ha hb
    | true =>
      simp only [d307574, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307575 q = 1) (hb : d332763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307575, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307575, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307581 q = 1) (hb : d332801 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307581, d332801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307581, d332801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307582 q = 1) (hb : d332802 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307582, d332802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307582, d332802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307583 q = 1) (hb : d332803 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307583, d332803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307583, d332803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307584 q = 1) (hb : d332804 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307584, d332804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307584, d332804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91010 (p : Pattern) (ha : d307623 p = 1) (hb : d332810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307618 q = 1) (hb : d332805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307618, d332805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91009 q ha hb
    | true =>
      simp only [d307618, d332805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307619 q = 1) (hb : d332806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307619, d332806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307619, d332806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307620 q = 1) (hb : d332807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307620, d332807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307620, d332807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307621 q = 1) (hb : d332808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307621, d332808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307621, d332808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307622 q = 1) (hb : d332809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307622, d332809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307622, d332809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307623 q = 1) (hb : d332810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307623, d332810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307623, d332810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91011 (p : Pattern) (ha : d307629 p = 1) (hb : d332816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307330 q = 1) (hb : d332546 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307330, d332546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307330, d332546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90962 q ha hb
  have h2 (q : Pattern) (ha : d307331 q = 1) (hb : d332547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307331, d332547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307331, d332547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307340 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307340, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90962 q ha hb
    | true =>
      simp only [d307340, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90965 q ha hb
  have h4 (q : Pattern) (ha : d307341 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307341, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307341, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307342 q = 1) (hb : d332558 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307342, d332558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307342, d332558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307465 q = 1) (hb : d332661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d332661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90982 q ha hb
    | true =>
      simp only [d307465, d332661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90989 q ha hb
  have h7 (q : Pattern) (ha : d307478 q = 1) (hb : d332674 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307478, d332674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90990 q ha hb
    | true =>
      simp only [d307478, d332674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90991 q ha hb
  have h8 (q : Pattern) (ha : d307479 q = 1) (hb : d332675 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d332675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307479, d332675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307480 q = 1) (hb : d332676 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d332676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307480, d332676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307481 q = 1) (hb : d332677 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d332677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307481, d332677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307485 q = 1) (hb : d332681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d332681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307485, d332681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90992 q ha hb
  have h12 (q : Pattern) (ha : d307487 q = 1) (hb : d332683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307487, d332683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307487, d332683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90993 q ha hb
  have h13 (q : Pattern) (ha : d307488 q = 1) (hb : d332684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d332684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307488, d332684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307489 q = 1) (hb : d332685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d332685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307489, d332685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307490 q = 1) (hb : d332686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d332686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307490, d332686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307491 q = 1) (hb : d332687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d332687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307491, d332687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307617 q = 1) (hb : d332800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d332800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307617, d332800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91008 q ha hb
  have h18 (q : Pattern) (ha : d307624 q = 1) (hb : d332811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307624, d332811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307624, d332811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91010 q ha hb
  have h19 (q : Pattern) (ha : d307625 q = 1) (hb : d332812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d332812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307625, d332812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307626 q = 1) (hb : d332813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d332813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307626, d332813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307627 q = 1) (hb : d332814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d332814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307627, d332814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307628 q = 1) (hb : d332815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d332815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307628, d332815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307629 q = 1) (hb : d332816 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d332816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307629, d332816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro91012 (p : Pattern) (ha : d307635 p = 1) (hb : d332822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d332817 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d332817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d332817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91011 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d332818 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d332818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d332818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d332819 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d332819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d332819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d332820 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d332820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d332820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d332821 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d332821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d332821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d332822 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d332822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d332822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91013 (p : Pattern) (ha : d38177 p = 1) (hb : d307643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d263572 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d307640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d307641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d307642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38177 q = 1) (hb : d307643 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38177, d307643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38177, d307643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro91014 (p : Pattern) (ha : d307658 p = 1) (hb : d332833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263571 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d263572 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d307640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d307641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d307642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d307650 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h9 (q : Pattern) (ha : d307651 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307651, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d307651, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307652 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307652, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307652, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307653 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d307654 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307654, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307654, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d307655 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307655, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307655, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d307656 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307656, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307656, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307657 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307657, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307657, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d307658 q = 1) (hb : d332833 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307658, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307658, d332833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro91015 (p : Pattern) (ha : d307664 p = 1) (hb : d332839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d307646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d307647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38302 q = 1) (hb : d307648 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38302, d307648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38302, d307648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307661 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307662 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307663 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307664 q = 1) (hb : d332839 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307664, d332839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d307664, d332839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91016 (p : Pattern) (ha : d307666 p = 1) (hb : d332841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d307646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d307647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307661 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307662 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307663 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307665 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307665, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307665, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307666 q = 1) (hb : d332841 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307666, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307666, d332841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91017 (p : Pattern) (ha : d307670 p = 1) (hb : d332845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5128 q = 1) (hb : d69215 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h3 (q : Pattern) (ha : d307651 q = 1) (hb : d332827 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307651, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307651, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307652 q = 1) (hb : d332828 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307652, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307652, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d307654 q = 1) (hb : d332829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d307654, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d307654, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307655 q = 1) (hb : d332830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d307655, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307655, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d307656 q = 1) (hb : d332831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d307656, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307656, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307657 q = 1) (hb : d332832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d307657, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307657, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d307670 q = 1) (hb : d332845 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307670, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307670, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro91018 (p : Pattern) (ha : d307676 p = 1) (hb : d332851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307661 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307662 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307665 q = 1) (hb : d332840 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307665, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307665, d332840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307671 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307671, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91017 q ha hb
    | true =>
      simp only [d307671, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307672 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307672, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307672, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307673 q = 1) (hb : d332848 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307673, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307673, d332848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307674 q = 1) (hb : d332849 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307674, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307674, d332849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307675 q = 1) (hb : d332850 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307675, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307675, d332850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307676 q = 1) (hb : d332851 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307676, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307676, d332851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91019 (p : Pattern) (ha : d307683 p = 1) (hb : d332858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307667 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91015 q ha hb
    | true =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
  have h2 (q : Pattern) (ha : d307668 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307669 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307677 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
    | true =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91018 q ha hb
  have h5 (q : Pattern) (ha : d307678 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307679 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307680 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307681 q = 1) (hb : d332856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307681, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307681, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307682 q = 1) (hb : d332857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307682, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307682, d332857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307683 q = 1) (hb : d332858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307683, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307683, d332858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro91020 (p : Pattern) (ha : d307687 p = 1) (hb : d332862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307677 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
    | true =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91018 q ha hb
  have h2 (q : Pattern) (ha : d307678 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307679 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307681 q = 1) (hb : d332856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307681, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307681, d332856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307686 q = 1) (hb : d332861 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307686, d332861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307686, d332861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307687 q = 1) (hb : d332862 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307687, d332862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307687, d332862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91021 (p : Pattern) (ha : d307693 p = 1) (hb : d332868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307691 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307692 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307692, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307692, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307693 q = 1) (hb : d332868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307693, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307693, d332868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91022 (p : Pattern) (ha : d307697 p = 1) (hb : d332872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307695 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307696 q = 1) (hb : d332871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307696, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307696, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307697 q = 1) (hb : d332872 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307697, d332872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307697, d332872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91023 (p : Pattern) (ha : d307703 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307698 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
    | true =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
  have h2 (q : Pattern) (ha : d307699 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307700 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307701 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307702 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307703 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307703, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307703, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91024 (p : Pattern) (ha : d307706 p = 1) (hb : d332881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307691 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307692 q = 1) (hb : d332867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307692, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307692, d332867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307706 q = 1) (hb : d332881 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307706, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307706, d332881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91025 (p : Pattern) (ha : d307707 p = 1) (hb : d332882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307695 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307696 q = 1) (hb : d332871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307696, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307696, d332871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307707 q = 1) (hb : d332882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307707, d332882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307707, d332882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91026 (p : Pattern) (ha : d307713 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307698 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
    | true =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
  have h2 (q : Pattern) (ha : d307699 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307700 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307701 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307702 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307708 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91024 q ha hb
    | true =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91025 q ha hb
  have h7 (q : Pattern) (ha : d307709 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307709, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307709, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307710 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307710, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307710, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307711 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307711, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307711, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307712 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307712, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307712, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307713 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307713, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307713, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91027 (p : Pattern) (ha : d307718 p = 1) (hb : d332893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307691 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307717 q = 1) (hb : d332892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307717, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307717, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307718 q = 1) (hb : d332893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307718, d332893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307718, d332893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91028 (p : Pattern) (ha : d307720 p = 1) (hb : d332895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307695 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307719 q = 1) (hb : d332894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307719, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307719, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307720 q = 1) (hb : d332895 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307720, d332895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307720, d332895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91029 (p : Pattern) (ha : d307727 p = 1) (hb : d332902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307725 q = 1) (hb : d332900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307725, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307725, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307726 q = 1) (hb : d332901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307726, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307726, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307727 q = 1) (hb : d332902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307727, d332902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307727, d332902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91030 (p : Pattern) (ha : d307730 p = 1) (hb : d332905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307728 q = 1) (hb : d332903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307728, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307728, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307729 q = 1) (hb : d332904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307729, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307729, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307730 q = 1) (hb : d332905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307730, d332905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307730, d332905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91031 (p : Pattern) (ha : d38303 p = 1) (hb : d307734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d307646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d307647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38302 q = 1) (hb : d307648 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38302, d307648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38302, d307648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38303 q = 1) (hb : d307734 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38303, d307734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38303, d307734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91032 (p : Pattern) (ha : d307740 p = 1) (hb : d332914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307735 q = 1) (hb : d332909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307735, d332909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91031 q hb ha
    | true =>
      simp only [d307735, d332909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91015 q ha hb
  have h2 (q : Pattern) (ha : d307736 q = 1) (hb : d332910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307736, d332910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307736, d332910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307737 q = 1) (hb : d332911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307737, d332911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307737, d332911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307667 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91015 q ha hb
    | true =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
  have h5 (q : Pattern) (ha : d307668 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307669 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307738 q = 1) (hb : d332912 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307738, d332912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307738, d332912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307677 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
    | true =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91018 q ha hb
  have h9 (q : Pattern) (ha : d307678 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307679 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307680 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307739 q = 1) (hb : d332913 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307739, d332913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307739, d332913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307740 q = 1) (hb : d332914 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307740, d332914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307740, d332914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro91033 (p : Pattern) (ha : d307746 p = 1) (hb : d332920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307741 q = 1) (hb : d332915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307741, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91032 q ha hb
    | true =>
      simp only [d307741, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307742 q = 1) (hb : d332916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307742, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307742, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307743 q = 1) (hb : d332917 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307743, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307743, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307744 q = 1) (hb : d332918 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307744, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307744, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307745 q = 1) (hb : d332919 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307745, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307745, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307746 q = 1) (hb : d332920 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307746, d332920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307746, d332920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91034 (p : Pattern) (ha : d307749 p = 1) (hb : d324966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263571 q = 1) : d0 q = 1 := by
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
  have h3 (q : Pattern) (ha : d38167 q = 1) (hb : d263572 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38167, d263572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38168 q = 1) (hb : d307640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38168, d307640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d38169 q = 1) (hb : d307641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38169, d307641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38170 q = 1) (hb : d307642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38170, d307642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d307749 q = 1) (hb : d324966 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d307749, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307749, d324966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro91035 (p : Pattern) (ha : d307755 p = 1) (hb : d332923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38180 q = 1) (hb : d307646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38180, d307646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38181 q = 1) (hb : d307647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38181, d307647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307661 q = 1) (hb : d332836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307661, d332836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307662 q = 1) (hb : d332837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307662, d332837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307663 q = 1) (hb : d332838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307663, d332838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307750 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
    | true =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307751 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307752 q = 1) (hb : d324969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307752, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307752, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307753 q = 1) (hb : d324970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307753, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307753, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307754 q = 1) (hb : d324971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307754, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307754, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307755 q = 1) (hb : d332923 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307755, d332923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307755, d332923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91036 (p : Pattern) (ha : d307756 p = 1) (hb : d324973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307750 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
    | true =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307751 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307752 q = 1) (hb : d324969 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307752, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307752, d324969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307753 q = 1) (hb : d324970 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307753, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307753, d324970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307754 q = 1) (hb : d324971 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307754, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307754, d324971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307756 q = 1) (hb : d324973 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307756, d324973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307756, d324973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91037 (p : Pattern) (ha : d307762 p = 1) (hb : d332929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307667 q = 1) (hb : d332842 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91015 q ha hb
    | true =>
      simp only [d307667, d332842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
  have h2 (q : Pattern) (ha : d307668 q = 1) (hb : d332843 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307668, d332843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307669 q = 1) (hb : d332844 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307669, d332844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307677 q = 1) (hb : d332852 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91016 q ha hb
    | true =>
      simp only [d307677, d332852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91018 q ha hb
  have h5 (q : Pattern) (ha : d307678 q = 1) (hb : d332853 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307678, d332853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307679 q = 1) (hb : d332854 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307679, d332854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307680 q = 1) (hb : d332855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307680, d332855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307757 q = 1) (hb : d332924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307757, d332924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91035 q ha hb
    | true =>
      simp only [d307757, d332924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91036 q ha hb
  have h9 (q : Pattern) (ha : d307758 q = 1) (hb : d332925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307758, d332925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307758, d332925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307759 q = 1) (hb : d332926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307759, d332926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307759, d332926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307760 q = 1) (hb : d332927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307760, d332927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307760, d332927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307761 q = 1) (hb : d332928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307761, d332928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307761, d332928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307762 q = 1) (hb : d332929 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307762, d332929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307762, d332929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro91038 (p : Pattern) (ha : d307768 p = 1) (hb : d332935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307763 q = 1) (hb : d332930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307763, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91037 q ha hb
    | true =>
      simp only [d307763, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307764 q = 1) (hb : d332931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307764, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307764, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307765 q = 1) (hb : d332932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307765, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307765, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307766 q = 1) (hb : d332933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307766, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307766, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307767 q = 1) (hb : d332934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307767, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307767, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307768 q = 1) (hb : d332935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307768, d332935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307768, d332935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91039 (p : Pattern) (ha : d307774 p = 1) (hb : d332941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307721 q = 1) (hb : d332896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307721, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91027 q ha hb
    | true =>
      simp only [d307721, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91028 q ha hb
  have h2 (q : Pattern) (ha : d307722 q = 1) (hb : d332897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307722, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307722, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307723 q = 1) (hb : d332898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307723, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307723, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307724 q = 1) (hb : d332899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307724, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307724, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307731 q = 1) (hb : d332906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307731, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91029 q ha hb
    | true =>
      simp only [d307731, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91030 q ha hb
  have h6 (q : Pattern) (ha : d307732 q = 1) (hb : d332907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307732, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307732, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307733 q = 1) (hb : d332908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307733, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307733, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307747 q = 1) (hb : d332921 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307747, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91033 q ha hb
    | true =>
      simp only [d307747, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d307748 q = 1) (hb : d332922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307748, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d307769 q = 1) (hb : d332936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307769, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91038 q ha hb
    | true =>
      simp only [d307769, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307770 q = 1) (hb : d332937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307770, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307770, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307771 q = 1) (hb : d332938 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307771, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307772 q = 1) (hb : d332939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307772, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307773 q = 1) (hb : d332940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307773, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307774 q = 1) (hb : d332941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307774, d332941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307774, d332941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro91040 (p : Pattern) (ha : d307775 p = 1) (hb : d332942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307691 q = 1) (hb : d332866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307691, d332866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307717 q = 1) (hb : d332892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307717, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307717, d332892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307775 q = 1) (hb : d332942 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307775, d332942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307775, d332942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91041 (p : Pattern) (ha : d307776 p = 1) (hb : d332943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307695 q = 1) (hb : d332870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307695, d332870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307719 q = 1) (hb : d332894 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307719, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307719, d332894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307776 q = 1) (hb : d332943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307776, d332943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307776, d332943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91042 (p : Pattern) (ha : d307781 p = 1) (hb : d332948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307690 q = 1) (hb : d332865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307690, d332865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307725 q = 1) (hb : d332900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307725, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307725, d332900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307726 q = 1) (hb : d332901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307726, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307726, d332901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307781 q = 1) (hb : d332948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307781, d332948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307781, d332948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91043 (p : Pattern) (ha : d307782 p = 1) (hb : d332949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307688 q = 1) (hb : d332863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91020 q ha hb
    | true =>
      simp only [d307688, d332863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307689 q = 1) (hb : d332864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307689, d332864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307694 q = 1) (hb : d332869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307694, d332869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307728 q = 1) (hb : d332903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307728, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307728, d332903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307729 q = 1) (hb : d332904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307729, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307729, d332904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307782 q = 1) (hb : d332949 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307782, d332949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307782, d332949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91044 (p : Pattern) (ha : d307786 p = 1) (hb : d332953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307741 q = 1) (hb : d332915 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307741, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91032 q ha hb
    | true =>
      simp only [d307741, d332915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307742 q = 1) (hb : d332916 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307742, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307742, d332916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307684 q = 1) (hb : d332859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91019 q ha hb
    | true =>
      simp only [d307684, d332859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307685 q = 1) (hb : d332860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307685, d332860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307743 q = 1) (hb : d332917 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307743, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307743, d332917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307744 q = 1) (hb : d332918 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307744, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307744, d332918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307745 q = 1) (hb : d332919 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307745, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307745, d332919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307786 q = 1) (hb : d332953 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307786, d332953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307786, d332953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91045 (p : Pattern) (ha : d307789 p = 1) (hb : d332956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307763 q = 1) (hb : d332930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307763, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91037 q ha hb
    | true =>
      simp only [d307763, d332930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307764 q = 1) (hb : d332931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307764, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307764, d332931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307765 q = 1) (hb : d332932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307765, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307765, d332932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307766 q = 1) (hb : d332933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307766, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307766, d332933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307767 q = 1) (hb : d332934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307767, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307767, d332934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307789 q = 1) (hb : d332956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307789, d332956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307789, d332956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91046 (p : Pattern) (ha : d307795 p = 1) (hb : d332962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307721 q = 1) (hb : d332896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307721, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91027 q ha hb
    | true =>
      simp only [d307721, d332896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91028 q ha hb
  have h2 (q : Pattern) (ha : d307722 q = 1) (hb : d332897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307722, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307722, d332897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307723 q = 1) (hb : d332898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307723, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307723, d332898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307724 q = 1) (hb : d332899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307724, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307724, d332899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307731 q = 1) (hb : d332906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307731, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91029 q ha hb
    | true =>
      simp only [d307731, d332906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91030 q ha hb
  have h6 (q : Pattern) (ha : d307732 q = 1) (hb : d332907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307732, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307732, d332907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307733 q = 1) (hb : d332908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307733, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307733, d332908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307747 q = 1) (hb : d332921 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307747, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91033 q ha hb
    | true =>
      simp only [d307747, d332921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d307748 q = 1) (hb : d332922 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307748, d332922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d307769 q = 1) (hb : d332936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307769, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91038 q ha hb
    | true =>
      simp only [d307769, d332936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307770 q = 1) (hb : d332937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307770, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307770, d332937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307771 q = 1) (hb : d332938 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307771, d332938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307772 q = 1) (hb : d332939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307772, d332939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307773 q = 1) (hb : d332940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307773, d332940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307777 q = 1) (hb : d332944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307777, d332944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91040 q ha hb
    | true =>
      simp only [d307777, d332944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91041 q ha hb
  have h17 (q : Pattern) (ha : d307778 q = 1) (hb : d332945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307778, d332945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307778, d332945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307779 q = 1) (hb : d332946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307779, d332946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307779, d332946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d307780 q = 1) (hb : d332947 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307780, d332947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307780, d332947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307783 q = 1) (hb : d332950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307783, d332950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91042 q ha hb
    | true =>
      simp only [d307783, d332950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91043 q ha hb
  have h21 (q : Pattern) (ha : d307784 q = 1) (hb : d332951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307784, d332951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307784, d332951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d307785 q = 1) (hb : d332952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307785, d332952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307785, d332952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307787 q = 1) (hb : d332954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307787, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91044 q ha hb
    | true =>
      simp only [d307787, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91024 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d307708 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d307788 q = 1) (hb : d332955 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d307788, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d307790 q = 1) (hb : d332957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307790, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91045 q ha hb
    | true =>
      simp only [d307790, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d307791 q = 1) (hb : d332958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307791, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d307791, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d307792 q = 1) (hb : d332959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d307792, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d307793 q = 1) (hb : d332960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307793, d332960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d307793, d332960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d307794 q = 1) (hb : d332961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307794, d332961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307794, d332961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d307795 q = 1) (hb : d332962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307795, d332962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307795, d332962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro91047 (p : Pattern) (ha : d307802 p = 1) (hb : d332969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307698 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
    | true =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
  have h2 (q : Pattern) (ha : d307699 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307699, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307700 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307700, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307701 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307701, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307702 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307702, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307797 q = 1) (hb : d332964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307797, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
    | true =>
      simp only [d307797, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307798 q = 1) (hb : d332965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307798, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307798, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307799 q = 1) (hb : d332966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307799, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307799, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307800 q = 1) (hb : d332967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307800, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307800, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307801 q = 1) (hb : d332968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307801, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307801, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307802 q = 1) (hb : d332969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307802, d332969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307802, d332969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91048 (p : Pattern) (ha : d307808 p = 1) (hb : d332975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307797 q = 1) (hb : d332964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307797, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
    | true =>
      simp only [d307797, d332964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307798 q = 1) (hb : d332965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307798, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307798, d332965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307799 q = 1) (hb : d332966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307799, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307799, d332966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307800 q = 1) (hb : d332967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307800, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307800, d332967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307801 q = 1) (hb : d332968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307801, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307801, d332968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307803 q = 1) (hb : d332970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307803, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91025 q ha hb
    | true =>
      simp only [d307803, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307804 q = 1) (hb : d332971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307804, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307804, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307805 q = 1) (hb : d332972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307805, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307805, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307806 q = 1) (hb : d332973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307806, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307806, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307807 q = 1) (hb : d332974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307807, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307807, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307808 q = 1) (hb : d332975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307808, d332975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307808, d332975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91049 (p : Pattern) (ha : d307815 p = 1) (hb : d332982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307787 q = 1) (hb : d332954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307787, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91044 q ha hb
    | true =>
      simp only [d307787, d332954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91024 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307708 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307788 q = 1) (hb : d332955 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307788, d332955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307790 q = 1) (hb : d332957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307790, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91045 q ha hb
    | true =>
      simp only [d307790, d332957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307791 q = 1) (hb : d332958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307791, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307791, d332958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307792 q = 1) (hb : d332959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307792, d332959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307813 q = 1) (hb : d332980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307813, d332980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307813, d332980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307814 q = 1) (hb : d332981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307814, d332981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307814, d332981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307815 q = 1) (hb : d332982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307815, d332982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307815, d332982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro91050 (p : Pattern) (ha : d307817 p = 1) (hb : d332984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307803 q = 1) (hb : d332970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307803, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91025 q ha hb
    | true =>
      simp only [d307803, d332970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307804 q = 1) (hb : d332971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307804, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307804, d332971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307805 q = 1) (hb : d332972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307805, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307805, d332972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307806 q = 1) (hb : d332973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307806, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307806, d332973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307807 q = 1) (hb : d332974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307807, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307807, d332974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307817 q = 1) (hb : d332984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307817, d332984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307817, d332984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91051 (p : Pattern) (ha : d38537 p = 1) (hb : d307828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d307823 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d307824 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d307825 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d307826 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38536 q = 1) (hb : d307827 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38536, d307827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38536, d307827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38537 q = 1) (hb : d307828 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38537, d307828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38537, d307828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91052 (p : Pattern) (ha : d307834 p = 1) (hb : d332995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d307823 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d307824 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d307825 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d307826 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38536 q = 1) (hb : d307827 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38536, d307827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38536, d307827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307829 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
  have h9 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307830 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307831 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307832 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307833 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307834 q = 1) (hb : d332995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307834, d332995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d307834, d332995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91053 (p : Pattern) (ha : d307839 p = 1) (hb : d333000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d307823 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d307824 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d307825 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d307826 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d307829 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
  have h8 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307830 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307831 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307832 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307833 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307838 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307838, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307838, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307839 q = 1) (hb : d333000 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307839, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307839, d333000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91054 (p : Pattern) (ha : d307849 p = 1) (hb : d333010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307829 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
  have h2 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307830 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307831 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307832 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307838 q = 1) (hb : d332999 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307838, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307838, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307844 q = 1) (hb : d333005 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307844, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307844, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91017 q ha hb
  have h9 (q : Pattern) (ha : d307671 q = 1) (hb : d332846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307671, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91017 q ha hb
    | true =>
      simp only [d307671, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307845 q = 1) (hb : d333006 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307845, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307845, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307672 q = 1) (hb : d332847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307672, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307672, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307846 q = 1) (hb : d333007 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307846, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307846, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307847 q = 1) (hb : d333008 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307847, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307847, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d307848 q = 1) (hb : d333009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307848, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307848, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307849 q = 1) (hb : d333010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307849, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307849, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91055 (p : Pattern) (ha : d307855 p = 1) (hb : d333016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307835 q = 1) (hb : d332996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307835, d332996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91051 q hb ha
    | true =>
      simp only [d307835, d332996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91052 q ha hb
  have h2 (q : Pattern) (ha : d307836 q = 1) (hb : d332997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307836, d332997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307836, d332997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307837 q = 1) (hb : d332998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307837, d332998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307837, d332998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307840 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91052 q ha hb
    | true =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
  have h5 (q : Pattern) (ha : d307841 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307842 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307843 q = 1) (hb : d333004 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307843, d333004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307843, d333004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307850 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
    | true =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91054 q ha hb
  have h9 (q : Pattern) (ha : d307851 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307852 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307853 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307854 q = 1) (hb : d333015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307854, d333015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307854, d333015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307855 q = 1) (hb : d333016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307855, d333016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307855, d333016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro91056 (p : Pattern) (ha : d307860 p = 1) (hb : d333021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307840 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91052 q ha hb
    | true =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
  have h2 (q : Pattern) (ha : d307841 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307842 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307850 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
    | true =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91054 q ha hb
  have h5 (q : Pattern) (ha : d307851 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307852 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307853 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307858 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307858, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307858, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307859 q = 1) (hb : d333020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307859, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307859, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307860 q = 1) (hb : d333021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307860, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307860, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro91057 (p : Pattern) (ha : d307866 p = 1) (hb : d333027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307856 q = 1) (hb : d333017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307856, d333017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91055 q ha hb
    | true =>
      simp only [d307856, d333017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307857 q = 1) (hb : d333018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307857, d333018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307857, d333018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307861 q = 1) (hb : d333022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307861, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91056 q ha hb
    | true =>
      simp only [d307861, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307862 q = 1) (hb : d333023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307862, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307862, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307863 q = 1) (hb : d333024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307863, d333024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307863, d333024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307864 q = 1) (hb : d333025 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307864, d333025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307864, d333025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307865 q = 1) (hb : d333026 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307865, d333026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307865, d333026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307866 q = 1) (hb : d333027 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307866, d333027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307866, d333027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91058 (p : Pattern) (ha : d307868 p = 1) (hb : d333029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307850 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
    | true =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91054 q ha hb
  have h2 (q : Pattern) (ha : d307851 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307852 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307858 q = 1) (hb : d333019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307858, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307858, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307867 q = 1) (hb : d333028 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307867, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307867, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307868 q = 1) (hb : d333029 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307868, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307868, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91059 (p : Pattern) (ha : d307874 p = 1) (hb : d333035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307861 q = 1) (hb : d333022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307861, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91056 q ha hb
    | true =>
      simp only [d307861, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307862 q = 1) (hb : d333023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307862, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307862, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307869 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307869, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91058 q ha hb
    | true =>
      simp only [d307869, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307870 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307870, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307870, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307871 q = 1) (hb : d333032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307871, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307871, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307872 q = 1) (hb : d333033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307872, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307872, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307873 q = 1) (hb : d333034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307873, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307873, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307874 q = 1) (hb : d333035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307874, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307874, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91060 (p : Pattern) (ha : d307887 p = 1) (hb : d333038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38532 q = 1) (hb : d307823 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38532, d307823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
  have h2 (q : Pattern) (ha : d38178 q = 1) (hb : d307644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91013 q ha hb
    | true =>
      simp only [d38178, d307644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38533 q = 1) (hb : d307824 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38533, d307824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38179 q = 1) (hb : d307645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38179, d307645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38534 q = 1) (hb : d307825 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38534, d307825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38535 q = 1) (hb : d307826 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38535, d307826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d307829 q = 1) (hb : d332990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307829, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
  have h8 (q : Pattern) (ha : d307659 q = 1) (hb : d332834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91014 q ha hb
    | true =>
      simp only [d307659, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d307830 q = 1) (hb : d332991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307830, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307660 q = 1) (hb : d332835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307660, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d307831 q = 1) (hb : d332992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307831, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d307832 q = 1) (hb : d332993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307832, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d307833 q = 1) (hb : d332994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d307833, d332994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307882 q = 1) (hb : d325083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307882, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307882, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
  have h15 (q : Pattern) (ha : d307750 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
    | true =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307883 q = 1) (hb : d325084 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307883, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307883, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307751 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d307884 q = 1) (hb : d325085 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307884, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307884, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d307885 q = 1) (hb : d325086 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307885, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d307885, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d307886 q = 1) (hb : d325087 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307886, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307886, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307887 q = 1) (hb : d333038 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307887, d333038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307887, d333038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro91061 (p : Pattern) (ha : d307888 p = 1) (hb : d325089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307882 q = 1) (hb : d325083 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307882, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307882, d325083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
  have h2 (q : Pattern) (ha : d307750 q = 1) (hb : d324967 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91034 q ha hb
    | true =>
      simp only [d307750, d324967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307883 q = 1) (hb : d325084 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307883, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307883, d325084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307751 q = 1) (hb : d324968 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307751, d324968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307884 q = 1) (hb : d325085 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d307884, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307884, d325085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307885 q = 1) (hb : d325086 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d307885, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307885, d325086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d307886 q = 1) (hb : d325087 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d307886, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307886, d325087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d307888 q = 1) (hb : d325089 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d307888, d325089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307888, d325089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro91062 (p : Pattern) (ha : d307894 p = 1) (hb : d333044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307840 q = 1) (hb : d333001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91052 q ha hb
    | true =>
      simp only [d307840, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
  have h2 (q : Pattern) (ha : d307841 q = 1) (hb : d333002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307841, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307842 q = 1) (hb : d333003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307842, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307850 q = 1) (hb : d333011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91053 q ha hb
    | true =>
      simp only [d307850, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91054 q ha hb
  have h5 (q : Pattern) (ha : d307851 q = 1) (hb : d333012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307851, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307852 q = 1) (hb : d333013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307852, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307853 q = 1) (hb : d333014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307853, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307889 q = 1) (hb : d333039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d307889, d333039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91060 q ha hb
    | true =>
      simp only [d307889, d333039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91061 q ha hb
  have h9 (q : Pattern) (ha : d307890 q = 1) (hb : d333040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d307890, d333040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307890, d333040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307891 q = 1) (hb : d333041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d307891, d333041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307891, d333041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307892 q = 1) (hb : d333042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d307892, d333042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307892, d333042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d307893 q = 1) (hb : d333043 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d307893, d333043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307893, d333043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307894 q = 1) (hb : d333044 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d307894, d333044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307894, d333044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro91063 (p : Pattern) (ha : d307900 p = 1) (hb : d333050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307895 q = 1) (hb : d333045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307895, d333045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91062 q ha hb
    | true =>
      simp only [d307895, d333045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307896 q = 1) (hb : d333046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307896, d333046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307896, d333046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307897 q = 1) (hb : d333047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307897, d333047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307897, d333047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307898 q = 1) (hb : d333048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307898, d333048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307898, d333048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307899 q = 1) (hb : d333049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307899, d333049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307899, d333049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307900 q = 1) (hb : d333050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307900, d333050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307900, d333050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91064 (p : Pattern) (ha : d307906 p = 1) (hb : d333056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307875 q = 1) (hb : d333036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307875, d333036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91057 q ha hb
    | true =>
      simp only [d307875, d333036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91059 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307881 q = 1) (hb : d333037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307881, d333037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307881, d333037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d307901 q = 1) (hb : d333051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307901, d333051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91063 q ha hb
    | true =>
      simp only [d307901, d333051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307902 q = 1) (hb : d333052 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307902, d333052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307902, d333052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307903 q = 1) (hb : d333053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307903, d333053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307903, d333053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307904 q = 1) (hb : d333054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307904, d333054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307904, d333054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307905 q = 1) (hb : d333055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307905, d333055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307905, d333055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307906 q = 1) (hb : d333056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307906, d333056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307906, d333056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro91065 (p : Pattern) (ha : d307879 p = 1) (hb : d333061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307869 q = 1) (hb : d333030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d307869, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91058 q ha hb
    | true =>
      simp only [d307869, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307870 q = 1) (hb : d333031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d307870, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307870, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307876 q = 1) (hb : d333058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d307876, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307876, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307877 q = 1) (hb : d333059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d307877, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307877, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307878 q = 1) (hb : d333060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d307878, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307878, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307879 q = 1) (hb : d333061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d307879, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307879, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91066 (p : Pattern) (ha : d307913 p = 1) (hb : d333067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307908 q = 1) (hb : d333062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307908, d333062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91065 q ha hb
    | true =>
      simp only [d307908, d333062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307909 q = 1) (hb : d333063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307909, d333063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307909, d333063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307910 q = 1) (hb : d333064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307910, d333064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307910, d333064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307911 q = 1) (hb : d333065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307911, d333065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307911, d333065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307912 q = 1) (hb : d333066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307912, d333066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307912, d333066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307913 q = 1) (hb : d333067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307913, d333067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307913, d333067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91067 (p : Pattern) (ha : d307919 p = 1) (hb : d333073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307704 q = 1) (hb : d332879 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307704, d332879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307704, d332879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91023 q ha hb
  have h2 (q : Pattern) (ha : d307705 q = 1) (hb : d332880 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307705, d332880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307705, d332880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307714 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307714, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91023 q ha hb
    | true =>
      simp only [d307714, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91026 q ha hb
  have h4 (q : Pattern) (ha : d307715 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307715, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307715, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307716 q = 1) (hb : d332891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307716, d332891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307716, d332891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307796 q = 1) (hb : d332963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307796, d332963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91039 q ha hb
    | true =>
      simp only [d307796, d332963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91046 q ha hb
  have h7 (q : Pattern) (ha : d307809 q = 1) (hb : d332976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307809, d332976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91047 q ha hb
    | true =>
      simp only [d307809, d332976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91048 q ha hb
  have h8 (q : Pattern) (ha : d307810 q = 1) (hb : d332977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307810, d332977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307810, d332977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307811 q = 1) (hb : d332978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307811, d332978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307811, d332978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307812 q = 1) (hb : d332979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307812, d332979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307812, d332979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307816 q = 1) (hb : d332983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307816, d332983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307816, d332983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91049 q ha hb
  have h12 (q : Pattern) (ha : d307818 q = 1) (hb : d332985 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307818, d332985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307818, d332985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91050 q ha hb
  have h13 (q : Pattern) (ha : d307819 q = 1) (hb : d332986 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307819, d332986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307819, d332986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307820 q = 1) (hb : d332987 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307820, d332987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307820, d332987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307821 q = 1) (hb : d332988 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307821, d332988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307821, d332988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307822 q = 1) (hb : d332989 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307822, d332989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307822, d332989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307907 q = 1) (hb : d333057 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307907, d333057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307907, d333057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91064 q ha hb
  have h18 (q : Pattern) (ha : d307914 q = 1) (hb : d333068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307914, d333068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307914, d333068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91066 q ha hb
  have h19 (q : Pattern) (ha : d307915 q = 1) (hb : d333069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307915, d333069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307915, d333069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d307916 q = 1) (hb : d333070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307916, d333070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307916, d333070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307917 q = 1) (hb : d333071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307917, d333071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307917, d333071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307918 q = 1) (hb : d333072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307918, d333072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307918, d333072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307919 q = 1) (hb : d333073 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307919, d333073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307919, d333073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro91068 (p : Pattern) (ha : d307925 p = 1) (hb : d333079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307920 q = 1) (hb : d333074 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307920, d333074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307920, d333074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91067 q ha hb
  have h2 (q : Pattern) (ha : d307921 q = 1) (hb : d333075 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307921, d333075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307921, d333075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307922 q = 1) (hb : d333076 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307922, d333076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307922, d333076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307923 q = 1) (hb : d333077 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307923, d333077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307923, d333077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307924 q = 1) (hb : d333078 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307924, d333078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307924, d333078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307925 q = 1) (hb : d333079 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307925, d333079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307925, d333079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91069 (p : Pattern) (ha : d307931 p = 1) (hb : d333085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d331804 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d331804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90780 q ha hb
    | true =>
      simp only [d306523, d331804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90827 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d332077 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d332077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d332077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90882 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d332078 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d332078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d332078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d332453 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d332453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d332453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90945 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d332454 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d332454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d332454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d332455 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d332455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d332455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d332823 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d332823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d332823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91012 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d332824 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d332824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d332824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d332825 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d332825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d332825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d332826 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d332826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d332826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d333080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d333080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d333080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91068 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d333081 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d333081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d333081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d333082 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d333082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d333082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d333083 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d333083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d333083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d333084 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d333084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d333084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d333085 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d333085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d333085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro91070 (p : Pattern) (ha : d307937 p = 1) (hb : d333091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d333086 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d333086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91069 q ha hb
    | true =>
      simp only [d307932, d333086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d333087 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d333087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d333087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d333088 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d333088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d333088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d333089 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d333089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d333089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d333090 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d333090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d333090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d333091 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d333091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d333091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91071 (p : Pattern) (ha : d307943 p = 1) (hb : d333097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d333092 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d333092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91070 q ha hb
    | true =>
      simp only [d307938, d333092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d333093 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d333093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d333093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d333094 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d333094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d333094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d333095 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d333095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d333095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d333096 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d333096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d333096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d333097 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d333097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d333097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91072 (p : Pattern) (ha : d307949 p = 1) (hb : d333103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d333098 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d333098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91071 q ha hb
    | true =>
      simp only [d307944, d333098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d333099 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d333099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d333099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d333100 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d333100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d333100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d333101 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d333101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d333101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d333102 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d333102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d333102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d333103 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d333103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d333103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91073 (p : Pattern) (ha : d307955 p = 1) (hb : d333109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d333104 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d333104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91072 q ha hb
    | true =>
      simp only [d307950, d333104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d333105 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d333105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d333105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d333106 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d333106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d333106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d333107 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d333107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d333107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d333108 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d333108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d333108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d333109 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d333109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d333109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91074 (p : Pattern) (ha : d307961 p = 1) (hb : d333115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d333110 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d333110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91073 q ha hb
    | true =>
      simp only [d307956, d333110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d333111 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d333111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d333111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d333112 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d333112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d333112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d333113 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d333113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d333113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d333114 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d333114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d333114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d333115 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d333115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d333115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91075 (p : Pattern) (ha : d307967 p = 1) (hb : d333121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d333116 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d333116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91074 q ha hb
    | true =>
      simp only [d307962, d333116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d333117 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d333117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d333117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d333118 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d333118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d333118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d333119 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d333119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d333119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d333120 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d333120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d333120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d333121 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d333121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d333121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91076 (p : Pattern) (ha : d307973 p = 1) (hb : d333127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d333122 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d333122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91075 q ha hb
    | true =>
      simp only [d307968, d333122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d333123 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d333123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d333123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d333124 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d333124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d333124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d333125 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d333125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d333125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d333126 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d333126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d333126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d333127 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d333127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d333127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91077 (p : Pattern) (ha : d270853 p = 1) (hb : d331335 p = 1) : d333130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d331335 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36033 q = 1) (hb : d331335 q = 1) : d331368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
    | true =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36093 q = 1) (hb : d331335 q = 1) : d331428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36093, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36094 q = 1) (hb : d331335 q = 1) : d331429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36094, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36095 q = 1) (hb : d331335 q = 1) : d331430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36096 q = 1) (hb : d331335 q = 1) : d331431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270853 q = 1) (hb : d331335 q = 1) : d333130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270853, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270853, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro91078 (p : Pattern) (ha : d270863 p = 1) (hb : d331335 p = 1) : d333140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d331335 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36069 q = 1) (hb : d331335 q = 1) : d331404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90397 q ha hb
    | true =>
      simp only [d36069, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270859 q = 1) (hb : d331335 q = 1) : d333136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270859, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270859, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270860 q = 1) (hb : d331335 q = 1) : d333137 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270860, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270860, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d270861 q = 1) (hb : d331335 q = 1) : d333138 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270861, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270861, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270862 q = 1) (hb : d331335 q = 1) : d333139 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270862, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270862, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270863 q = 1) (hb : d331335 q = 1) : d333140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270863, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270863, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro91079 (p : Pattern) (ha : d270869 p = 1) (hb : d331335 p = 1) : d333146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36098 q = 1) (hb : d331335 q = 1) : d331433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90400 q ha hb
    | true =>
      simp only [d36098, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90401 q ha hb
  have h2 (q : Pattern) (ha : d36099 q = 1) (hb : d331335 q = 1) : d331434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36099, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270851 q = 1) (hb : d331335 q = 1) : d333128 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270851, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270851, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270852 q = 1) (hb : d331335 q = 1) : d333129 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270852, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270852, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270854 q = 1) (hb : d331335 q = 1) : d333131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270854, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270854, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91077 q ha hb
  have h6 (q : Pattern) (ha : d270855 q = 1) (hb : d331335 q = 1) : d333132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270855, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270855, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270856 q = 1) (hb : d331335 q = 1) : d333133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270856, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270856, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270857 q = 1) (hb : d331335 q = 1) : d333134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270857, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270857, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270858 q = 1) (hb : d331335 q = 1) : d333135 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270858, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270858, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270864 q = 1) (hb : d331335 q = 1) : d333141 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270864, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270864, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91078 q ha hb
  have h11 (q : Pattern) (ha : d270865 q = 1) (hb : d331335 q = 1) : d333142 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270865, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270865, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270866 q = 1) (hb : d331335 q = 1) : d333143 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270866, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270866, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270867 q = 1) (hb : d331335 q = 1) : d333144 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270867, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270867, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270868 q = 1) (hb : d331335 q = 1) : d333145 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270868, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270868, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270869 q = 1) (hb : d331335 q = 1) : d333146 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270869, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270869, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91080 (p : Pattern) (ha : d270875 p = 1) (hb : d331335 p = 1) : d333152 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d331335 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270870 q = 1) (hb : d331335 q = 1) : d333147 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270870, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270870, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91079 q ha hb
  have h3 (q : Pattern) (ha : d270871 q = 1) (hb : d331335 q = 1) : d333148 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270871, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270871, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270872 q = 1) (hb : d331335 q = 1) : d333149 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270872, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270872, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270873 q = 1) (hb : d331335 q = 1) : d333150 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270873, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270873, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270874 q = 1) (hb : d331335 q = 1) : d333151 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270874, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270874, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270875 q = 1) (hb : d331335 q = 1) : d333152 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270875, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270875, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro91081 (p : Pattern) (ha : d270878 p = 1) (hb : d331335 p = 1) : d333155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36307 q = 1) (hb : d331335 q = 1) : d331600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90431 q ha hb
    | true =>
      simp only [d36307, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90432 q ha hb
  have h2 (q : Pattern) (ha : d36308 q = 1) (hb : d331335 q = 1) : d331601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36308, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36309 q = 1) (hb : d331335 q = 1) : d331602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36309, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36310 q = 1) (hb : d331335 q = 1) : d331603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36311 q = 1) (hb : d331335 q = 1) : d331604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270878 q = 1) (hb : d331335 q = 1) : d333155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270878, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270878, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91082 (p : Pattern) (ha : d270889 p = 1) (hb : d331335 p = 1) : d333166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270884 q = 1) (hb : d331335 q = 1) : d333161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270884, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90467 q ha hb
    | true =>
      simp only [d270884, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90438 q ha hb
  have h2 (q : Pattern) (ha : d270885 q = 1) (hb : d331335 q = 1) : d333162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270885, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270885, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270886 q = 1) (hb : d331335 q = 1) : d333163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270886, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270886, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270887 q = 1) (hb : d331335 q = 1) : d333164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270887, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270887, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270888 q = 1) (hb : d331335 q = 1) : d333165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270888, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270888, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270889 q = 1) (hb : d331335 q = 1) : d333166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270889, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270889, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91083 (p : Pattern) (ha : d270895 p = 1) (hb : d331335 p = 1) : d333172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36313 q = 1) (hb : d331335 q = 1) : d331606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90430 q ha hb
    | true =>
      simp only [d36313, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90433 q ha hb
  have h2 (q : Pattern) (ha : d36314 q = 1) (hb : d331335 q = 1) : d331607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36314, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270876 q = 1) (hb : d331335 q = 1) : d333153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270876, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270876, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270877 q = 1) (hb : d331335 q = 1) : d333154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270877, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270877, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270879 q = 1) (hb : d331335 q = 1) : d333156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270879, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270879, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91081 q ha hb
  have h6 (q : Pattern) (ha : d270880 q = 1) (hb : d331335 q = 1) : d333157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270880, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270880, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270881 q = 1) (hb : d331335 q = 1) : d333158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270881, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270881, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270882 q = 1) (hb : d331335 q = 1) : d333159 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270882, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270882, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270883 q = 1) (hb : d331335 q = 1) : d333160 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270883, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270883, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270890 q = 1) (hb : d331335 q = 1) : d333167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270890, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270890, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91082 q ha hb
  have h11 (q : Pattern) (ha : d270891 q = 1) (hb : d331335 q = 1) : d333168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270891, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270891, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270892 q = 1) (hb : d331335 q = 1) : d333169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270892, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270892, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270893 q = 1) (hb : d331335 q = 1) : d333170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270893, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270893, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270894 q = 1) (hb : d331335 q = 1) : d333171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270894, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270894, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270895 q = 1) (hb : d331335 q = 1) : d333172 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270895, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270895, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91084 (p : Pattern) (ha : d270901 p = 1) (hb : d331335 p = 1) : d333178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270896 q = 1) (hb : d331335 q = 1) : d333173 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270896, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270896, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91083 q ha hb
  have h2 (q : Pattern) (ha : d270897 q = 1) (hb : d331335 q = 1) : d333174 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270897, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270897, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270898 q = 1) (hb : d331335 q = 1) : d333175 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270898, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270898, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270899 q = 1) (hb : d331335 q = 1) : d333176 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270899, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270899, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270900 q = 1) (hb : d331335 q = 1) : d333177 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270900, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270900, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270901 q = 1) (hb : d331335 q = 1) : d333178 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270901, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270901, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91085 (p : Pattern) (ha : d270905 p = 1) (hb : d331335 p = 1) : d333182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36639 q = 1) (hb : d331335 q = 1) : d331850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90481 q ha hb
    | true =>
      simp only [d36639, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90482 q ha hb
  have h2 (q : Pattern) (ha : d36640 q = 1) (hb : d331335 q = 1) : d331851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36640, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36641 q = 1) (hb : d331335 q = 1) : d331852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36641, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36642 q = 1) (hb : d331335 q = 1) : d331853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36643 q = 1) (hb : d331335 q = 1) : d331854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270905 q = 1) (hb : d331335 q = 1) : d333182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270905, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270905, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91086 (p : Pattern) (ha : d270916 p = 1) (hb : d331335 p = 1) : d333193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270911 q = 1) (hb : d331335 q = 1) : d333188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270911, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90521 q ha hb
    | true =>
      simp only [d270911, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90490 q ha hb
  have h2 (q : Pattern) (ha : d270912 q = 1) (hb : d331335 q = 1) : d333189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270912, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270912, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270913 q = 1) (hb : d331335 q = 1) : d333190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270913, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270913, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270914 q = 1) (hb : d331335 q = 1) : d333191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270914, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270914, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270915 q = 1) (hb : d331335 q = 1) : d333192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270915, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270915, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270916 q = 1) (hb : d331335 q = 1) : d333193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270916, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270916, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91087 (p : Pattern) (ha : d270922 p = 1) (hb : d331335 p = 1) : d333199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36645 q = 1) (hb : d331335 q = 1) : d331856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36645, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90480 q ha hb
    | true =>
      simp only [d36645, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90483 q ha hb
  have h2 (q : Pattern) (ha : d36646 q = 1) (hb : d331335 q = 1) : d331857 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36646, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36646, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270903 q = 1) (hb : d331335 q = 1) : d333180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270903, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270903, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270904 q = 1) (hb : d331335 q = 1) : d333181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270904, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270904, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270906 q = 1) (hb : d331335 q = 1) : d333183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270906, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270906, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91085 q ha hb
  have h6 (q : Pattern) (ha : d270907 q = 1) (hb : d331335 q = 1) : d333184 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270907, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270907, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270908 q = 1) (hb : d331335 q = 1) : d333185 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270908, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270908, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270909 q = 1) (hb : d331335 q = 1) : d333186 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270909, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270909, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270910 q = 1) (hb : d331335 q = 1) : d333187 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270910, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270910, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270917 q = 1) (hb : d331335 q = 1) : d333194 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270917, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270917, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91086 q ha hb
  have h11 (q : Pattern) (ha : d270918 q = 1) (hb : d331335 q = 1) : d333195 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270918, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270918, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270919 q = 1) (hb : d331335 q = 1) : d333196 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270919, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270919, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270920 q = 1) (hb : d331335 q = 1) : d333197 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270920, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270920, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270921 q = 1) (hb : d331335 q = 1) : d333198 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270921, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270921, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270922 q = 1) (hb : d331335 q = 1) : d333199 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270922, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270922, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91088 (p : Pattern) (ha : d270928 p = 1) (hb : d331335 p = 1) : d333205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270923 q = 1) (hb : d331335 q = 1) : d333200 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270923, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270923, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91087 q ha hb
  have h2 (q : Pattern) (ha : d270924 q = 1) (hb : d331335 q = 1) : d333201 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270924, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270924, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270925 q = 1) (hb : d331335 q = 1) : d333202 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270925, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270925, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270926 q = 1) (hb : d331335 q = 1) : d333203 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270926, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270926, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270927 q = 1) (hb : d331335 q = 1) : d333204 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270927, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270927, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270928 q = 1) (hb : d331335 q = 1) : d333205 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270928, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270928, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91089 (p : Pattern) (ha : d270933 p = 1) (hb : d331335 p = 1) : d333210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37070 q = 1) (hb : d331335 q = 1) : d332178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90540 q ha hb
    | true =>
      simp only [d37070, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90541 q ha hb
  have h2 (q : Pattern) (ha : d37071 q = 1) (hb : d331335 q = 1) : d332179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37071, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37072 q = 1) (hb : d331335 q = 1) : d332180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37072, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37073 q = 1) (hb : d331335 q = 1) : d332181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37074 q = 1) (hb : d331335 q = 1) : d332182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270933 q = 1) (hb : d331335 q = 1) : d333210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270933, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270933, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91090 (p : Pattern) (ha : d270944 p = 1) (hb : d331335 p = 1) : d333221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270939 q = 1) (hb : d331335 q = 1) : d333216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270939, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90581 q ha hb
    | true =>
      simp only [d270939, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90549 q ha hb
  have h2 (q : Pattern) (ha : d270940 q = 1) (hb : d331335 q = 1) : d333217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270940, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270940, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270941 q = 1) (hb : d331335 q = 1) : d333218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270941, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270941, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270942 q = 1) (hb : d331335 q = 1) : d333219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270942, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270942, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270943 q = 1) (hb : d331335 q = 1) : d333220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270943, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270943, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270944 q = 1) (hb : d331335 q = 1) : d333221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270944, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270944, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91091 (p : Pattern) (ha : d270950 p = 1) (hb : d331335 p = 1) : d333227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d331335 q = 1) : d332184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90539 q ha hb
    | true =>
      simp only [d37076, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90542 q ha hb
  have h2 (q : Pattern) (ha : d37077 q = 1) (hb : d331335 q = 1) : d332185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270931 q = 1) (hb : d331335 q = 1) : d333208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270931, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270931, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270932 q = 1) (hb : d331335 q = 1) : d333209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270932, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270932, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270934 q = 1) (hb : d331335 q = 1) : d333211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270934, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270934, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91089 q ha hb
  have h6 (q : Pattern) (ha : d270935 q = 1) (hb : d331335 q = 1) : d333212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270935, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270935, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270936 q = 1) (hb : d331335 q = 1) : d333213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270936, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270936, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270937 q = 1) (hb : d331335 q = 1) : d333214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270937, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270937, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270938 q = 1) (hb : d331335 q = 1) : d333215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270938, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270938, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270945 q = 1) (hb : d331335 q = 1) : d333222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270945, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270945, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91090 q ha hb
  have h11 (q : Pattern) (ha : d270946 q = 1) (hb : d331335 q = 1) : d333223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270946, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270946, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270947 q = 1) (hb : d331335 q = 1) : d333224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270947, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270947, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270948 q = 1) (hb : d331335 q = 1) : d333225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270948, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270948, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270949 q = 1) (hb : d331335 q = 1) : d333226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270949, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270949, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270950 q = 1) (hb : d331335 q = 1) : d333227 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270950, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270950, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91092 (p : Pattern) (ha : d270956 p = 1) (hb : d331335 p = 1) : d333233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270951 q = 1) (hb : d331335 q = 1) : d333228 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270951, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270951, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91091 q ha hb
  have h2 (q : Pattern) (ha : d270952 q = 1) (hb : d331335 q = 1) : d333229 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270952, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270952, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270953 q = 1) (hb : d331335 q = 1) : d333230 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270953, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270953, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270954 q = 1) (hb : d331335 q = 1) : d333231 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270954, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270954, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270955 q = 1) (hb : d331335 q = 1) : d333232 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270955, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270955, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270956 q = 1) (hb : d331335 q = 1) : d333233 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270956, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270956, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91093 (p : Pattern) (ha : d324280 p = 1) (hb : d331335 p = 1) : d333239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37632 q = 1) (hb : d331335 q = 1) : d332550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37632, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90607 q ha hb
    | true =>
      simp only [d37632, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90608 q ha hb
  have h2 (q : Pattern) (ha : d37633 q = 1) (hb : d331335 q = 1) : d332551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37633, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37633, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37634 q = 1) (hb : d331335 q = 1) : d332552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37634, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37634, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37635 q = 1) (hb : d331335 q = 1) : d332553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37635, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37635, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37636 q = 1) (hb : d331335 q = 1) : d332554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37636, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37636, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324280 q = 1) (hb : d331335 q = 1) : d333239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324280, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324280, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91094 (p : Pattern) (ha : d324287 p = 1) (hb : d331335 p = 1) : d332753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37980 q = 1) (hb : d331335 q = 1) : d332738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37980, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90648 q ha hb
    | true =>
      simp only [d37980, d332738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90615 q ha hb
  have h2 (q : Pattern) (ha : d37981 q = 1) (hb : d331335 q = 1) : d332739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37981, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37981, d332739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37982 q = 1) (hb : d331335 q = 1) : d332740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37982, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37982, d332740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d37994 q = 1) (hb : d331335 q = 1) : d332743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37994, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90615 q ha hb
    | true =>
      simp only [d37994, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90650 q ha hb
  have h5 (q : Pattern) (ha : d37995 q = 1) (hb : d331335 q = 1) : d332744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37995, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37995, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37996 q = 1) (hb : d331335 q = 1) : d332745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37996, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37996, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37997 q = 1) (hb : d331335 q = 1) : d332746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37997, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37997, d332746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38013 q = 1) (hb : d331335 q = 1) : d332743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38013, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90615 q ha hb
    | true =>
      simp only [d38013, d332743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90616 q ha hb
  have h9 (q : Pattern) (ha : d38014 q = 1) (hb : d331335 q = 1) : d332744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38014, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38014, d332744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38015 q = 1) (hb : d331335 q = 1) : d332745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38015, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38015, d332745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38016 q = 1) (hb : d331335 q = 1) : d332751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38016, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38016, d332751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324286 q = 1) (hb : d331335 q = 1) : d332752 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324286, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324286, d332752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324287 q = 1) (hb : d331335 q = 1) : d332753 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324287, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324287, d332753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro91095 (p : Pattern) (ha : d324293 p = 1) (hb : d331335 p = 1) : d332767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324288 q = 1) (hb : d331335 q = 1) : d332754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324288, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91094 q ha hb
    | true =>
      simp only [d324288, d332754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324289 q = 1) (hb : d331335 q = 1) : d332755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324289, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324289, d332755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38019 q = 1) (hb : d331335 q = 1) : d332762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38019, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90617 q ha hb
    | true =>
      simp only [d38019, d332762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38020 q = 1) (hb : d331335 q = 1) : d332763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38020, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38020, d332763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324290 q = 1) (hb : d331335 q = 1) : d332764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324290, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324290, d332764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324291 q = 1) (hb : d331335 q = 1) : d332765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324291, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324291, d332765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324292 q = 1) (hb : d331335 q = 1) : d332766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324292, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324292, d332766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324293 q = 1) (hb : d331335 q = 1) : d332767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324293, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324293, d332767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91096 (p : Pattern) (ha : d324299 p = 1) (hb : d331335 p = 1) : d333250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324294 q = 1) (hb : d331335 q = 1) : d333245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324294, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91095 q ha hb
    | true =>
      simp only [d324294, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90618 q ha hb
  have h2 (q : Pattern) (ha : d324295 q = 1) (hb : d331335 q = 1) : d333246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324295, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324295, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324296 q = 1) (hb : d331335 q = 1) : d333247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324296, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324296, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324297 q = 1) (hb : d331335 q = 1) : d333248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324297, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324297, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324298 q = 1) (hb : d331335 q = 1) : d333249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324298, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324298, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324299 q = 1) (hb : d331335 q = 1) : d333250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324299, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324299, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91097 (p : Pattern) (ha : d324305 p = 1) (hb : d331335 p = 1) : d333256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37638 q = 1) (hb : d331335 q = 1) : d332556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37638, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90606 q ha hb
    | true =>
      simp only [d37638, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90609 q ha hb
  have h2 (q : Pattern) (ha : d37639 q = 1) (hb : d331335 q = 1) : d332557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37639, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37639, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324278 q = 1) (hb : d331335 q = 1) : d333237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324278, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324278, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324279 q = 1) (hb : d331335 q = 1) : d333238 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324279, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324279, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324281 q = 1) (hb : d331335 q = 1) : d333240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324281, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324281, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91093 q ha hb
  have h6 (q : Pattern) (ha : d324282 q = 1) (hb : d331335 q = 1) : d333241 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324282, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324282, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324283 q = 1) (hb : d331335 q = 1) : d333242 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324283, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324283, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324284 q = 1) (hb : d331335 q = 1) : d333243 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324284, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324284, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d324285 q = 1) (hb : d331335 q = 1) : d333244 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324285, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324285, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324300 q = 1) (hb : d331335 q = 1) : d333251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324300, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324300, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91096 q ha hb
  have h11 (q : Pattern) (ha : d324301 q = 1) (hb : d331335 q = 1) : d333252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324301, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324301, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324302 q = 1) (hb : d331335 q = 1) : d333253 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324302, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324302, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324303 q = 1) (hb : d331335 q = 1) : d333254 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324303, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324303, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d324304 q = 1) (hb : d331335 q = 1) : d333255 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324304, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324304, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324305 q = 1) (hb : d331335 q = 1) : d333256 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324305, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324305, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91098 (p : Pattern) (ha : d324311 p = 1) (hb : d331335 p = 1) : d333262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324306 q = 1) (hb : d331335 q = 1) : d333257 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324306, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324306, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91097 q ha hb
  have h2 (q : Pattern) (ha : d324307 q = 1) (hb : d331335 q = 1) : d333258 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324307, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324307, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324308 q = 1) (hb : d331335 q = 1) : d333259 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324308, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324308, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324309 q = 1) (hb : d331335 q = 1) : d333260 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324309, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324309, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324310 q = 1) (hb : d331335 q = 1) : d333261 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324310, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324310, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324311 q = 1) (hb : d331335 q = 1) : d333262 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324311, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324311, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91099 (p : Pattern) (ha : d324318 p = 1) (hb : d331335 p = 1) : d333269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38276 q = 1) (hb : d331335 q = 1) : d332883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38276, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90683 q ha hb
    | true =>
      simp only [d38276, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90684 q ha hb
  have h2 (q : Pattern) (ha : d38277 q = 1) (hb : d331335 q = 1) : d332884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38277, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38277, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38278 q = 1) (hb : d331335 q = 1) : d332885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38278, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38278, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38279 q = 1) (hb : d331335 q = 1) : d332886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38279, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38279, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38280 q = 1) (hb : d331335 q = 1) : d332887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38280, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38280, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324318 q = 1) (hb : d331335 q = 1) : d333269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324318, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324318, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91100 (p : Pattern) (ha : d324325 p = 1) (hb : d331335 p = 1) : d333021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38572 q = 1) (hb : d331335 q = 1) : d333001 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38572, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90719 q ha hb
    | true =>
      simp only [d38572, d333001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90691 q ha hb
  have h2 (q : Pattern) (ha : d38573 q = 1) (hb : d331335 q = 1) : d333002 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38573, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38573, d333002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38574 q = 1) (hb : d331335 q = 1) : d333003 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38574, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38574, d333003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38586 q = 1) (hb : d331335 q = 1) : d333011 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38586, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90691 q ha hb
    | true =>
      simp only [d38586, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90721 q ha hb
  have h5 (q : Pattern) (ha : d38587 q = 1) (hb : d331335 q = 1) : d333012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38587, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38587, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38588 q = 1) (hb : d331335 q = 1) : d333013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38588, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38588, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38589 q = 1) (hb : d331335 q = 1) : d333014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38589, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38589, d333014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38605 q = 1) (hb : d331335 q = 1) : d333011 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38605, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90691 q ha hb
    | true =>
      simp only [d38605, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90692 q ha hb
  have h9 (q : Pattern) (ha : d38606 q = 1) (hb : d331335 q = 1) : d333012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38606, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38606, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38607 q = 1) (hb : d331335 q = 1) : d333013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38607, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38607, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38608 q = 1) (hb : d331335 q = 1) : d333019 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38608, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38608, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324324 q = 1) (hb : d331335 q = 1) : d333020 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324324, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324324, d333020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324325 q = 1) (hb : d331335 q = 1) : d333021 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324325, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324325, d333021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro91101 (p : Pattern) (ha : d324331 p = 1) (hb : d331335 p = 1) : d333035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324326 q = 1) (hb : d331335 q = 1) : d333022 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324326, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91100 q ha hb
    | true =>
      simp only [d324326, d333022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324327 q = 1) (hb : d331335 q = 1) : d333023 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324327, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324327, d333023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38611 q = 1) (hb : d331335 q = 1) : d333030 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38611, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90693 q ha hb
    | true =>
      simp only [d38611, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38612 q = 1) (hb : d331335 q = 1) : d333031 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38612, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38612, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324328 q = 1) (hb : d331335 q = 1) : d333032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324328, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324328, d333032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324329 q = 1) (hb : d331335 q = 1) : d333033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324329, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324329, d333033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324330 q = 1) (hb : d331335 q = 1) : d333034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324330, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324330, d333034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324331 q = 1) (hb : d331335 q = 1) : d333035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324331, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324331, d333035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91102 (p : Pattern) (ha : d324333 p = 1) (hb : d331335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46865 q = 1) (hb : d253504 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d46865, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d324332 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d324332, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324332, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44880 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44880, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46865 q = 1) (hb : d331334 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d331334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46865, d331334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d253504 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d46866 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46866, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d324333 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91103 (p : Pattern) (ha : d324339 p = 1) (hb : d331335 p = 1) : d332845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90667 q ha hb
  have h2 (q : Pattern) (ha : d324334 q = 1) (hb : d331335 q = 1) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d324334, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91102 q ha hb
    | true =>
      simp only [d324334, d5128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90666 q ha hb
  have h3 (q : Pattern) (ha : d324335 q = 1) (hb : d331335 q = 1) : d332827 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d324335, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324335, d332827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324336 q = 1) (hb : d331335 q = 1) : d332828 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d324336, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324336, d332828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90667 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10406 q = 1) (hb : d331335 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90666 q ha hb
    | true =>
      simp only [d10406, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38188 q = 1) (hb : d331335 q = 1) : d332829 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38188, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38188, d332829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38189 q = 1) (hb : d331335 q = 1) : d332830 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38189, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38189, d332830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d324337 q = 1) (hb : d331335 q = 1) : d332831 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d324337, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324337, d332831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324338 q = 1) (hb : d331335 q = 1) : d332832 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d324338, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324338, d332832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d324339 q = 1) (hb : d331335 q = 1) : d332845 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d324339, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324339, d332845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro91104 (p : Pattern) (ha : d324345 p = 1) (hb : d331335 p = 1) : d333010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38566 q = 1) (hb : d331335 q = 1) : d332990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38566, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38566, d332990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90672 q ha hb
  have h2 (q : Pattern) (ha : d38211 q = 1) (hb : d331335 q = 1) : d332834 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38211, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90672 q ha hb
    | true =>
      simp only [d38211, d332834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38567 q = 1) (hb : d331335 q = 1) : d332991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38567, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38567, d332991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38212 q = 1) (hb : d331335 q = 1) : d332835 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38212, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38212, d332835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38568 q = 1) (hb : d331335 q = 1) : d332992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38568, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38568, d332992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38569 q = 1) (hb : d331335 q = 1) : d332993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38569, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38569, d332993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38603 q = 1) (hb : d331335 q = 1) : d332999 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38603, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38603, d332999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38580 q = 1) (hb : d331335 q = 1) : d333005 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38580, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38580, d333005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90675 q ha hb
  have h9 (q : Pattern) (ha : d38234 q = 1) (hb : d331335 q = 1) : d332846 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38234, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90675 q ha hb
    | true =>
      simp only [d38234, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d38581 q = 1) (hb : d331335 q = 1) : d333006 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38581, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38581, d333006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d324340 q = 1) (hb : d331335 q = 1) : d332846 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d324340, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91103 q ha hb
    | true =>
      simp only [d324340, d332846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324341 q = 1) (hb : d331335 q = 1) : d332847 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d324341, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324341, d332847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324342 q = 1) (hb : d331335 q = 1) : d333007 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d324342, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324342, d333007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d324343 q = 1) (hb : d331335 q = 1) : d333008 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d324343, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324343, d333008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324344 q = 1) (hb : d331335 q = 1) : d333009 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d324344, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d324344, d333009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d324345 q = 1) (hb : d331335 q = 1) : d333010 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324345, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324345, d333010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro91105 (p : Pattern) (ha : d324351 p = 1) (hb : d331335 p = 1) : d333029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324346 q = 1) (hb : d331335 q = 1) : d333011 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d324346, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90691 q ha hb
    | true =>
      simp only [d324346, d333011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91104 q ha hb
  have h2 (q : Pattern) (ha : d324347 q = 1) (hb : d331335 q = 1) : d333012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d324347, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324347, d333012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324348 q = 1) (hb : d331335 q = 1) : d333013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d324348, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324348, d333013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324349 q = 1) (hb : d331335 q = 1) : d333019 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d324349, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324349, d333019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324350 q = 1) (hb : d331335 q = 1) : d333028 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324350, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324350, d333028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324351 q = 1) (hb : d331335 q = 1) : d333029 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324351, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324351, d333029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91106 (p : Pattern) (ha : d324357 p = 1) (hb : d331335 p = 1) : d333061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324352 q = 1) (hb : d331335 q = 1) : d333030 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324352, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91105 q ha hb
    | true =>
      simp only [d324352, d333030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324353 q = 1) (hb : d331335 q = 1) : d333031 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324353, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324353, d333031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324354 q = 1) (hb : d331335 q = 1) : d333058 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324354, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324354, d333058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324355 q = 1) (hb : d331335 q = 1) : d333059 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324355, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324355, d333059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324356 q = 1) (hb : d331335 q = 1) : d333060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324356, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324356, d333060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324357 q = 1) (hb : d331335 q = 1) : d333061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324357, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324357, d333061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91107 (p : Pattern) (ha : d324363 p = 1) (hb : d331335 p = 1) : d333280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324358 q = 1) (hb : d331335 q = 1) : d333275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324358, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91101 q ha hb
    | true =>
      simp only [d324358, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91106 q ha hb
  have h2 (q : Pattern) (ha : d324359 q = 1) (hb : d331335 q = 1) : d333276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324359, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324359, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324360 q = 1) (hb : d331335 q = 1) : d333277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324360, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324360, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324361 q = 1) (hb : d331335 q = 1) : d333278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324361, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324361, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324362 q = 1) (hb : d331335 q = 1) : d333279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324362, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324362, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324363 q = 1) (hb : d331335 q = 1) : d333280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324363, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324363, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91108 (p : Pattern) (ha : d324369 p = 1) (hb : d331335 p = 1) : d333286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38282 q = 1) (hb : d331335 q = 1) : d332889 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38282, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90682 q ha hb
    | true =>
      simp only [d38282, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90685 q ha hb
  have h2 (q : Pattern) (ha : d38283 q = 1) (hb : d331335 q = 1) : d332890 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38283, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38283, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324316 q = 1) (hb : d331335 q = 1) : d333267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324316, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324316, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324317 q = 1) (hb : d331335 q = 1) : d333268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324317, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324317, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324319 q = 1) (hb : d331335 q = 1) : d333270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324319, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324319, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91099 q ha hb
  have h6 (q : Pattern) (ha : d324320 q = 1) (hb : d331335 q = 1) : d333271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324320, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324320, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324321 q = 1) (hb : d331335 q = 1) : d333272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324321, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324321, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d324322 q = 1) (hb : d331335 q = 1) : d333273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324322, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324322, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d324323 q = 1) (hb : d331335 q = 1) : d333274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324323, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324323, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324364 q = 1) (hb : d331335 q = 1) : d333281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324364, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324364, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91107 q ha hb
  have h11 (q : Pattern) (ha : d324365 q = 1) (hb : d331335 q = 1) : d333282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324365, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324365, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d324366 q = 1) (hb : d331335 q = 1) : d333283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324366, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324366, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d324367 q = 1) (hb : d331335 q = 1) : d333284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324367, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324367, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d324368 q = 1) (hb : d331335 q = 1) : d333285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324368, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324368, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d324369 q = 1) (hb : d331335 q = 1) : d333286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324369, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324369, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91109 (p : Pattern) (ha : d324375 p = 1) (hb : d331335 p = 1) : d333292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324370 q = 1) (hb : d331335 q = 1) : d333287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324370, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324370, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91108 q ha hb
  have h2 (q : Pattern) (ha : d324371 q = 1) (hb : d331335 q = 1) : d333288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324371, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324371, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d324372 q = 1) (hb : d331335 q = 1) : d333289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324372, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324372, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d324373 q = 1) (hb : d331335 q = 1) : d333290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324373, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324373, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d324374 q = 1) (hb : d331335 q = 1) : d333291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324374, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324374, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d324375 q = 1) (hb : d331335 q = 1) : d333292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324375, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d324375, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91110 (p : Pattern) (ha : d324381 p = 1) (hb : d331335 p = 1) : d333298 p = 1 := by
  have h0 (q : Pattern) (ha : d270902 q = 1) (hb : d331335 q = 1) : d333179 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270902, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91080 q ha hb
    | true =>
      simp only [d270902, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91084 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270929 q = 1) (hb : d331335 q = 1) : d333206 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270929, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270929, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91088 q ha hb
  have h3 (q : Pattern) (ha : d270930 q = 1) (hb : d331335 q = 1) : d333207 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270930, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270930, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270957 q = 1) (hb : d331335 q = 1) : d333234 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270957, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270957, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91092 q ha hb
  have h5 (q : Pattern) (ha : d270958 q = 1) (hb : d331335 q = 1) : d333235 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270958, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270958, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270959 q = 1) (hb : d331335 q = 1) : d333236 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270959, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270959, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d324312 q = 1) (hb : d331335 q = 1) : d333263 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324312, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324312, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91098 q ha hb
  have h8 (q : Pattern) (ha : d324313 q = 1) (hb : d331335 q = 1) : d333264 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324313, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324313, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d324314 q = 1) (hb : d331335 q = 1) : d333265 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324314, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324314, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d324315 q = 1) (hb : d331335 q = 1) : d333266 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324315, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324315, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d324376 q = 1) (hb : d331335 q = 1) : d333293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324376, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324376, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91109 q ha hb
  have h12 (q : Pattern) (ha : d324377 q = 1) (hb : d331335 q = 1) : d333294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324377, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324377, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d324378 q = 1) (hb : d331335 q = 1) : d333295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324378, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324378, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d324379 q = 1) (hb : d331335 q = 1) : d333296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324379, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324379, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d324380 q = 1) (hb : d331335 q = 1) : d333297 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d324380, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324380, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d324381 q = 1) (hb : d331335 q = 1) : d333298 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d324381, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d324381, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro91111 (p : Pattern) (ha : d324387 p = 1) (hb : d331335 p = 1) : d333304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324382 q = 1) (hb : d331335 q = 1) : d333299 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d324382, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91110 q ha hb
    | true =>
      simp only [d324382, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324383 q = 1) (hb : d331335 q = 1) : d333300 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d324383, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324383, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324384 q = 1) (hb : d331335 q = 1) : d333301 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d324384, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324384, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324385 q = 1) (hb : d331335 q = 1) : d333302 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d324385, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324385, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324386 q = 1) (hb : d331335 q = 1) : d333303 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d324386, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324386, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324387 q = 1) (hb : d331335 q = 1) : d333304 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d324387, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324387, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91112 (p : Pattern) (ha : d324393 p = 1) (hb : d331335 p = 1) : d333310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324388 q = 1) (hb : d331335 q = 1) : d333305 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d324388, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91111 q ha hb
    | true =>
      simp only [d324388, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324389 q = 1) (hb : d331335 q = 1) : d333306 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d324389, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324389, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324390 q = 1) (hb : d331335 q = 1) : d333307 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d324390, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324390, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324391 q = 1) (hb : d331335 q = 1) : d333308 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d324391, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324391, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324392 q = 1) (hb : d331335 q = 1) : d333309 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d324392, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324392, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324393 q = 1) (hb : d331335 q = 1) : d333310 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d324393, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324393, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91113 (p : Pattern) (ha : d324399 p = 1) (hb : d331335 p = 1) : d333316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324394 q = 1) (hb : d331335 q = 1) : d333311 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d324394, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91112 q ha hb
    | true =>
      simp only [d324394, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324395 q = 1) (hb : d331335 q = 1) : d333312 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d324395, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324395, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324396 q = 1) (hb : d331335 q = 1) : d333313 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d324396, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324396, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324397 q = 1) (hb : d331335 q = 1) : d333314 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d324397, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324397, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324398 q = 1) (hb : d331335 q = 1) : d333315 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d324398, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324398, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324399 q = 1) (hb : d331335 q = 1) : d333316 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d324399, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324399, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91114 (p : Pattern) (ha : d324405 p = 1) (hb : d331335 p = 1) : d333322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324400 q = 1) (hb : d331335 q = 1) : d333317 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d324400, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91113 q ha hb
    | true =>
      simp only [d324400, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324401 q = 1) (hb : d331335 q = 1) : d333318 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d324401, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324401, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324402 q = 1) (hb : d331335 q = 1) : d333319 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d324402, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324402, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324403 q = 1) (hb : d331335 q = 1) : d333320 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d324403, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324403, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324404 q = 1) (hb : d331335 q = 1) : d333321 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d324404, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324404, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324405 q = 1) (hb : d331335 q = 1) : d333322 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d324405, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324405, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91115 (p : Pattern) (ha : d324411 p = 1) (hb : d331335 p = 1) : d333328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324406 q = 1) (hb : d331335 q = 1) : d333323 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d324406, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91114 q ha hb
    | true =>
      simp only [d324406, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324407 q = 1) (hb : d331335 q = 1) : d333324 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d324407, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324407, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324408 q = 1) (hb : d331335 q = 1) : d333325 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d324408, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324408, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324409 q = 1) (hb : d331335 q = 1) : d333326 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d324409, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324409, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324410 q = 1) (hb : d331335 q = 1) : d333327 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d324410, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324410, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324411 q = 1) (hb : d331335 q = 1) : d333328 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d324411, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324411, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91116 (p : Pattern) (ha : d324417 p = 1) (hb : d331335 p = 1) : d333334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324412 q = 1) (hb : d331335 q = 1) : d333329 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d324412, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91115 q ha hb
    | true =>
      simp only [d324412, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324413 q = 1) (hb : d331335 q = 1) : d333330 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d324413, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324413, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324414 q = 1) (hb : d331335 q = 1) : d333331 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d324414, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324414, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324415 q = 1) (hb : d331335 q = 1) : d333332 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d324415, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324415, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324416 q = 1) (hb : d331335 q = 1) : d333333 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d324416, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324416, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324417 q = 1) (hb : d331335 q = 1) : d333334 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d324417, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324417, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91117 (p : Pattern) (ha : d324423 p = 1) (hb : d331335 p = 1) : d333340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324418 q = 1) (hb : d331335 q = 1) : d333335 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d324418, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91116 q ha hb
    | true =>
      simp only [d324418, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324419 q = 1) (hb : d331335 q = 1) : d333336 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d324419, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324419, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324420 q = 1) (hb : d331335 q = 1) : d333337 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d324420, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324420, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324421 q = 1) (hb : d331335 q = 1) : d333338 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d324421, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324421, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324422 q = 1) (hb : d331335 q = 1) : d333339 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d324422, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324422, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324423 q = 1) (hb : d331335 q = 1) : d333340 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d324423, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324423, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91118 (p : Pattern) (ha : d306197 p = 1) (hb : d331425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306064 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90745 q ha hb
    | true =>
      simp only [d306064, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d306187 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306187, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306194 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306194, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306195 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306195, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306196 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306196, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306197 q = 1) (hb : d331425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306197, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306197, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91119 (p : Pattern) (ha : d306216 p = 1) (hb : d331432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306064 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90745 q ha hb
    | true =>
      simp only [d306064, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d306187 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306187, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306194 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306194, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306195 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306195, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306196 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306196, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306202 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306206 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306071 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90747 q ha hb
    | true =>
      simp only [d306071, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d306209 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306209, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306213 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306213, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306214 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306214, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306214, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306215 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306215, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306215, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306216 q = 1) (hb : d331432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306216, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306216, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91120 (p : Pattern) (ha : d306225 p = 1) (hb : d333130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306071 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90747 q ha hb
    | true =>
      simp only [d306071, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d306209 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306209, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306213 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306213, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306223 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306223, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306223, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306224 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306224, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306224, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306225 q = 1) (hb : d333130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306225, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306225, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91121 (p : Pattern) (ha : d306265 p = 1) (hb : d333140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306107 q = 1) (hb : d331404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306107, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90752 q ha hb
    | true =>
      simp only [d306107, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d306255 q = 1) (hb : d333136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306255, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306255, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306261 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306262 q = 1) (hb : d333137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306262, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306262, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306263 q = 1) (hb : d333138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306263, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306263, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306264 q = 1) (hb : d333139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306264, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306264, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306265 q = 1) (hb : d333140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306265, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306265, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91122 (p : Pattern) (ha : d306271 p = 1) (hb : d333146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306217 q = 1) (hb : d331433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306217, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91118 q ha hb
    | true =>
      simp only [d306217, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306220 q = 1) (hb : d331434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306220, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306220, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306221 q = 1) (hb : d333128 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306221, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306221, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306222 q = 1) (hb : d333129 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306222, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306222, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306226 q = 1) (hb : d333131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306226, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306226, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91120 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306227 q = 1) (hb : d333132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306227, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306227, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306228 q = 1) (hb : d333133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306228, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306228, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306229 q = 1) (hb : d333134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306229, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306229, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306230 q = 1) (hb : d333135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306230, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306230, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306266 q = 1) (hb : d333141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306266, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306266, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91121 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306267 q = 1) (hb : d333142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306267, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306267, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306268 q = 1) (hb : d333143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306268, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306268, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306269 q = 1) (hb : d333144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306269, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306269, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306270 q = 1) (hb : d333145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306270, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306270, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306271 q = 1) (hb : d333146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306271, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306271, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91123 (p : Pattern) (ha : d306277 p = 1) (hb : d333152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d306119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80480 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d306120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d306121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d306122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d306123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306272 q = 1) (hb : d333147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306272, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306272, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91122 q ha hb
  have h8 (q : Pattern) (ha : d306273 q = 1) (hb : d333148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306273, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306273, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306274 q = 1) (hb : d333149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306274, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306274, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306275 q = 1) (hb : d333150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306275, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306275, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306276 q = 1) (hb : d333151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306276, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306276, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306277 q = 1) (hb : d333152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306277, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d306277, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro91124 (p : Pattern) (ha : d306394 p = 1) (hb : d331595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306295 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90783 q ha hb
    | true =>
      simp only [d306295, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90784 q ha hb
  have h5 (q : Pattern) (ha : d306384 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306384, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306391 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306391, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306392 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306392, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306393 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306393, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306394 q = 1) (hb : d331595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306394, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306394, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91125 (p : Pattern) (ha : d306415 p = 1) (hb : d331605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306295 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90783 q ha hb
    | true =>
      simp only [d306295, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90784 q ha hb
  have h4 (q : Pattern) (ha : d306384 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306384, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306391 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306391, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306392 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306392, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306393 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306393, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306400 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306405 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306305 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90786 q ha hb
    | true =>
      simp only [d306305, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90787 q ha hb
  have h13 (q : Pattern) (ha : d306408 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306408, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306412 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306412, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306413 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306413, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306413, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306414 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306414, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306414, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306415 q = 1) (hb : d331605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306415, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306415, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91126 (p : Pattern) (ha : d306435 p = 1) (hb : d333155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306305 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90786 q ha hb
    | true =>
      simp only [d306305, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90787 q ha hb
  have h3 (q : Pattern) (ha : d306408 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306408, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306412 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306412, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306433 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306433, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306433, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306434 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306434, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306434, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306435 q = 1) (hb : d333155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306435, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306435, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91127 (p : Pattern) (ha : d306503 p = 1) (hb : d333166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306492 q = 1) (hb : d333161 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306492, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90821 q ha hb
    | true =>
      simp only [d306492, d333161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90824 q ha hb
  have h3 (q : Pattern) (ha : d306493 q = 1) (hb : d333162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306493, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306493, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306500 q = 1) (hb : d333163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306500, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306500, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306501 q = 1) (hb : d333164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306501, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306501, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306502 q = 1) (hb : d333165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306502, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306502, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306503 q = 1) (hb : d333166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306503, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306503, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91128 (p : Pattern) (ha : d306516 p = 1) (hb : d333172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306416 q = 1) (hb : d331606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306416, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91124 q ha hb
    | true =>
      simp only [d306416, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91125 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306430 q = 1) (hb : d331607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306430, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306430, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306431 q = 1) (hb : d333153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306431, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306431, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306432 q = 1) (hb : d333154 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306432, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306432, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306436 q = 1) (hb : d333156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306436, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306436, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91126 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306438 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306439 q = 1) (hb : d333157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306439, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306439, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306440 q = 1) (hb : d333158 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306440, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306440, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306441 q = 1) (hb : d333159 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306441, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306441, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306442 q = 1) (hb : d333160 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306442, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306442, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306504 q = 1) (hb : d333167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306504, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306504, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91127 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306512 q = 1) (hb : d333168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306512, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306512, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306513 q = 1) (hb : d333169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306513, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306513, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306514 q = 1) (hb : d333170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306514, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306514, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306515 q = 1) (hb : d333171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306515, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306515, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306516 q = 1) (hb : d333172 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306516, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306516, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91129 (p : Pattern) (ha : d306522 p = 1) (hb : d333178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306517 q = 1) (hb : d333173 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306517, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306517, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91128 q ha hb
  have h2 (q : Pattern) (ha : d306518 q = 1) (hb : d333174 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306518, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306518, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306519 q = 1) (hb : d333175 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306519, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306519, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306520 q = 1) (hb : d333176 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306520, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306520, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306521 q = 1) (hb : d333177 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306521, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306521, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306522 q = 1) (hb : d333178 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306522, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306522, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91130 (p : Pattern) (ha : d306670 p = 1) (hb : d331845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306559 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90834 q ha hb
    | true =>
      simp only [d306559, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90835 q ha hb
  have h5 (q : Pattern) (ha : d306660 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306660, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306667 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306667, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306668 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306668, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306669 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306669, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306670 q = 1) (hb : d331845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306670, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306670, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91131 (p : Pattern) (ha : d306691 p = 1) (hb : d331855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306559 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90834 q ha hb
    | true =>
      simp only [d306559, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90835 q ha hb
  have h4 (q : Pattern) (ha : d306660 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306660, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306667 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306667, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306668 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306668, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306669 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306669, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306676 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306681 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306569 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90837 q ha hb
    | true =>
      simp only [d306569, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90838 q ha hb
  have h13 (q : Pattern) (ha : d306684 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306684, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306688 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306688, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306689 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306689, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306689, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306690 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306690, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306690, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306691 q = 1) (hb : d331855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306691, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306691, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91132 (p : Pattern) (ha : d306711 p = 1) (hb : d333182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306569 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90837 q ha hb
    | true =>
      simp only [d306569, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90838 q ha hb
  have h3 (q : Pattern) (ha : d306684 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306684, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306688 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306688, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306709 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306709, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306709, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306710 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306710, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306710, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306711 q = 1) (hb : d333182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306711, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306711, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91133 (p : Pattern) (ha : d306796 p = 1) (hb : d333193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306785 q = 1) (hb : d333188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306785, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90876 q ha hb
    | true =>
      simp only [d306785, d333188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90879 q ha hb
  have h3 (q : Pattern) (ha : d306786 q = 1) (hb : d333189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306786, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306786, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306793 q = 1) (hb : d333190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306793, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306793, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306794 q = 1) (hb : d333191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306794, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306794, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306795 q = 1) (hb : d333192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306795, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306795, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306796 q = 1) (hb : d333193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306796, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306796, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91134 (p : Pattern) (ha : d306809 p = 1) (hb : d333199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306692 q = 1) (hb : d331856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306692, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91130 q ha hb
    | true =>
      simp only [d306692, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91131 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306706 q = 1) (hb : d331857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306706, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306706, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306707 q = 1) (hb : d333180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306707, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306707, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306708 q = 1) (hb : d333181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306708, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306708, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306712 q = 1) (hb : d333183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306712, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306712, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91132 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306715 q = 1) (hb : d333184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306715, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306715, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306716 q = 1) (hb : d333185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306716, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306716, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306717 q = 1) (hb : d333186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306717, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306717, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306718 q = 1) (hb : d333187 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306718, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306718, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306797 q = 1) (hb : d333194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306797, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306797, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91133 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306804 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306805 q = 1) (hb : d333195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306805, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306805, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306806 q = 1) (hb : d333196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306806, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306806, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306807 q = 1) (hb : d333197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306807, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306807, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306808 q = 1) (hb : d333198 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306808, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306808, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306809 q = 1) (hb : d333199 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306809, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306809, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91135 (p : Pattern) (ha : d306815 p = 1) (hb : d333205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306810 q = 1) (hb : d333200 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306810, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306810, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91134 q ha hb
  have h2 (q : Pattern) (ha : d306811 q = 1) (hb : d333201 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306811, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306811, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306812 q = 1) (hb : d333202 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306812, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306812, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306813 q = 1) (hb : d333203 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306813, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306813, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306814 q = 1) (hb : d333204 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306814, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306814, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306815 q = 1) (hb : d333205 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306815, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306815, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91136 (p : Pattern) (ha : d307028 p = 1) (hb : d332173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306909 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90894 q ha hb
    | true =>
      simp only [d306909, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90895 q ha hb
  have h5 (q : Pattern) (ha : d307009 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307009, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307025 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307025, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307026 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307026, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307027 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307027, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307028 q = 1) (hb : d332173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307028, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307028, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91137 (p : Pattern) (ha : d307049 p = 1) (hb : d332183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306909 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90894 q ha hb
    | true =>
      simp only [d306909, d332168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90895 q ha hb
  have h4 (q : Pattern) (ha : d307009 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307009, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307025 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307025, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307026 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307026, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307027 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307027, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306919 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90897 q ha hb
    | true =>
      simp only [d306919, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90898 q ha hb
  have h13 (q : Pattern) (ha : d307042 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307042, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307046 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307046, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307047 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307047, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307047, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307048 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307048, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307048, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307049 q = 1) (hb : d332183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307049, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307049, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91138 (p : Pattern) (ha : d307069 p = 1) (hb : d333210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306919 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90897 q ha hb
    | true =>
      simp only [d306919, d332178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90898 q ha hb
  have h3 (q : Pattern) (ha : d307042 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307042, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307046 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307046, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307067 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307067, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307067, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307068 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307068, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307068, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307069 q = 1) (hb : d333210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307069, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307069, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91139 (p : Pattern) (ha : d307190 p = 1) (hb : d333221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307170 q = 1) (hb : d333216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307170, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90937 q ha hb
    | true =>
      simp only [d307170, d333216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90942 q ha hb
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d333217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307171, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307187 q = 1) (hb : d333218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307188 q = 1) (hb : d333219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307189 q = 1) (hb : d333220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307190 q = 1) (hb : d333221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91140 (p : Pattern) (ha : d307203 p = 1) (hb : d333227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307050 q = 1) (hb : d332184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91136 q ha hb
    | true =>
      simp only [d307050, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91137 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307064 q = 1) (hb : d332185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307064, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307065 q = 1) (hb : d333208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307065, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307066 q = 1) (hb : d333209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307066, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307070 q = 1) (hb : d333211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307070, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91138 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307073 q = 1) (hb : d333212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307073, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307074 q = 1) (hb : d333213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307074, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307075 q = 1) (hb : d333214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307075, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307076 q = 1) (hb : d333215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307076, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307191 q = 1) (hb : d333222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307191, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91139 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307199 q = 1) (hb : d333223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307199, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307200 q = 1) (hb : d333224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307200, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307201 q = 1) (hb : d333225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307201, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307202 q = 1) (hb : d333226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307202, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307203 q = 1) (hb : d333227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307203, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91141 (p : Pattern) (ha : d307209 p = 1) (hb : d333233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d333228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91140 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d333229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d333230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d333231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d333232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d333233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91142 (p : Pattern) (ha : d307443 p = 1) (hb : d332545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307324 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90960 q ha hb
    | true =>
      simp only [d307324, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90961 q ha hb
  have h5 (q : Pattern) (ha : d307411 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307411, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307440 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307440, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307441 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307441, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307442 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307442, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307443 q = 1) (hb : d332545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307443, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307443, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91143 (p : Pattern) (ha : d307464 p = 1) (hb : d332555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307324 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90960 q ha hb
    | true =>
      simp only [d307324, d332540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90961 q ha hb
  have h4 (q : Pattern) (ha : d307411 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307411, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307440 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307440, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307441 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307441, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307442 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307442, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307449 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307334 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90963 q ha hb
    | true =>
      simp only [d307334, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90964 q ha hb
  have h13 (q : Pattern) (ha : d307457 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307457, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307461 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307461, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307462 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307462, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307462, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307463 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307463, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307463, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307464 q = 1) (hb : d332555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307464, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307464, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91144 (p : Pattern) (ha : d307484 p = 1) (hb : d333239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307334 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90963 q ha hb
    | true =>
      simp only [d307334, d332550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90964 q ha hb
  have h3 (q : Pattern) (ha : d307457 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307457, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307461 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307461, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307482 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307482, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307482, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307483 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307483, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307483, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307484 q = 1) (hb : d333239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91145 (p : Pattern) (ha : d307616 p = 1) (hb : d333250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307585 q = 1) (hb : d333245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307585, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91003 q ha hb
    | true =>
      simp only [d307585, d333245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91009 q ha hb
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d333246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307613 q = 1) (hb : d333247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307614 q = 1) (hb : d333248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307615 q = 1) (hb : d333249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307616 q = 1) (hb : d333250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91146 (p : Pattern) (ha : d307629 p = 1) (hb : d333256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307465 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91142 q ha hb
    | true =>
      simp only [d307465, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91143 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307479 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307479, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307480 q = 1) (hb : d333237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307480, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307481 q = 1) (hb : d333238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307481, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307485 q = 1) (hb : d333240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307485, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91144 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307488 q = 1) (hb : d333241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307488, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307489 q = 1) (hb : d333242 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307489, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307490 q = 1) (hb : d333243 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307490, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307491 q = 1) (hb : d333244 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307491, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307617 q = 1) (hb : d333251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307617, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91145 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307625 q = 1) (hb : d333252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307625, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307626 q = 1) (hb : d333253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307626, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307627 q = 1) (hb : d333254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307627, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307628 q = 1) (hb : d333255 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307628, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307629 q = 1) (hb : d333256 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307629, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91147 (p : Pattern) (ha : d307635 p = 1) (hb : d333262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d333257 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91146 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d333258 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d333259 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d333260 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d333261 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d333262 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91148 (p : Pattern) (ha : d307774 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307698 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
    | true =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
  have h5 (q : Pattern) (ha : d307748 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307748, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307771 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307771, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307772 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307772, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307773 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307773, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307774 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307774, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307774, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91149 (p : Pattern) (ha : d307795 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307698 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91021 q ha hb
    | true =>
      simp only [d307698, d332873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91022 q ha hb
  have h4 (q : Pattern) (ha : d307748 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307748, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307748, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307771 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307771, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307771, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307772 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307772, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307772, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307773 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307773, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307773, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307708 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91024 q ha hb
    | true =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91025 q ha hb
  have h13 (q : Pattern) (ha : d307788 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307788, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307792 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307792, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307793 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307793, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307793, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307794 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307794, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307794, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307795 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307795, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307795, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91150 (p : Pattern) (ha : d307815 p = 1) (hb : d333269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307708 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91024 q ha hb
    | true =>
      simp only [d307708, d332883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91025 q ha hb
  have h3 (q : Pattern) (ha : d307788 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307788, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307788, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307792 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307792, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307792, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307813 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307813, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307813, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307814 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307814, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307814, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307815 q = 1) (hb : d333269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307815, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307815, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91151 (p : Pattern) (ha : d307906 p = 1) (hb : d333280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307880 q = 1) (hb : d333275 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307880, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91059 q ha hb
    | true =>
      simp only [d307880, d333275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91065 q ha hb
  have h3 (q : Pattern) (ha : d307881 q = 1) (hb : d333276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307881, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307881, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307903 q = 1) (hb : d333277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307903, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307903, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307904 q = 1) (hb : d333278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307904, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307904, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307905 q = 1) (hb : d333279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307905, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307905, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307906 q = 1) (hb : d333280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307906, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307906, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91152 (p : Pattern) (ha : d307919 p = 1) (hb : d333286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307716 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307796 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307796, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91148 q ha hb
    | true =>
      simp only [d307796, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91149 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307810 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307810, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307810, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307811 q = 1) (hb : d333267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307811, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307811, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307812 q = 1) (hb : d333268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307812, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307812, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307816 q = 1) (hb : d333270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307816, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307816, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91150 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307819 q = 1) (hb : d333271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307819, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307819, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307820 q = 1) (hb : d333272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307820, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307820, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307821 q = 1) (hb : d333273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307821, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307821, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307822 q = 1) (hb : d333274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307822, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307822, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307907 q = 1) (hb : d333281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307907, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307907, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91151 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307915 q = 1) (hb : d333282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307915, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307915, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307916 q = 1) (hb : d333283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307916, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307916, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307917 q = 1) (hb : d333284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307917, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307917, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307918 q = 1) (hb : d333285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307918, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307918, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307919 q = 1) (hb : d333286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307919, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307919, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91153 (p : Pattern) (ha : d307925 p = 1) (hb : d333292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307920 q = 1) (hb : d333287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307920, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307920, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91152 q ha hb
  have h2 (q : Pattern) (ha : d307921 q = 1) (hb : d333288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307921, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307921, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307922 q = 1) (hb : d333289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307922, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307922, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307923 q = 1) (hb : d333290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307923, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307923, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307924 q = 1) (hb : d333291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307924, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307924, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307925 q = 1) (hb : d333292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307925, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307925, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91154 (p : Pattern) (ha : d307931 p = 1) (hb : d333298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d333179 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91123 q ha hb
    | true =>
      simp only [d306523, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91129 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d333206 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91135 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d333207 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d333234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91141 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d333235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d333236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d333263 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91147 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d333264 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d333265 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d333266 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d333293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91153 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d333294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d333295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d333296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d333297 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d333298 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro91155 (p : Pattern) (ha : d307937 p = 1) (hb : d333304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d333299 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91154 q ha hb
    | true =>
      simp only [d307932, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d333300 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d333301 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d333302 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d333303 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d333304 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91156 (p : Pattern) (ha : d307943 p = 1) (hb : d333310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d333305 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91155 q ha hb
    | true =>
      simp only [d307938, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d333306 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d333307 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d333308 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d333309 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d333310 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91157 (p : Pattern) (ha : d307949 p = 1) (hb : d333316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d333311 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91156 q ha hb
    | true =>
      simp only [d307944, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d333312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d333313 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d333314 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d333315 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d333316 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91158 (p : Pattern) (ha : d307955 p = 1) (hb : d333322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d333317 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91157 q ha hb
    | true =>
      simp only [d307950, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d333318 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d333319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d333320 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d333321 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d333322 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91159 (p : Pattern) (ha : d307961 p = 1) (hb : d333328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d333323 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91158 q ha hb
    | true =>
      simp only [d307956, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d333324 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d333325 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d333326 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d333327 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d333328 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91160 (p : Pattern) (ha : d307967 p = 1) (hb : d333334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d333329 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91159 q ha hb
    | true =>
      simp only [d307962, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d333330 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d333331 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d333332 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d333333 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d333334 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91161 (p : Pattern) (ha : d307973 p = 1) (hb : d333340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d333335 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91160 q ha hb
    | true =>
      simp only [d307968, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d333336 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d333337 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d333338 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d333339 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d333340 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro91162 (p : Pattern) (ha : d309471 p = 1) (hb : d332878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309467 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309467, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309468 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309468, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309469 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309469, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309470 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309470, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309471 q = 1) (hb : d332878 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309471, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309471, d332878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91163 (p : Pattern) (ha : d309476 p = 1) (hb : d332888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332873 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309467 q = 1) (hb : d332874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309467, d332874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309468 q = 1) (hb : d332875 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309468, d332875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309469 q = 1) (hb : d332876 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309469, d332876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309470 q = 1) (hb : d332877 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309470, d332877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44640 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44645 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309472 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309472, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309473 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309473, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309474 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309474, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309474, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309475 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309475, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309475, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309476 q = 1) (hb : d332888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309476, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309476, d332888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91164 (p : Pattern) (ha : d309483 p = 1) (hb : d333269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309472 q = 1) (hb : d332884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309472, d332884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309473 q = 1) (hb : d332885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309473, d332885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309481 q = 1) (hb : d332886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309481, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309481, d332886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309482 q = 1) (hb : d332887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309482, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309482, d332887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309483 q = 1) (hb : d333269 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309483, d333269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91165 (p : Pattern) (ha : d309493 p = 1) (hb : d333280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44738 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333275 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309489 q = 1) (hb : d333276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309489, d333276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44804 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309490 q = 1) (hb : d333277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309490, d333277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309491 q = 1) (hb : d333278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309491, d333278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309492 q = 1) (hb : d333279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309492, d333279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309493 q = 1) (hb : d333280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309493, d333280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91166 (p : Pattern) (ha : d309499 p = 1) (hb : d333286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309477 q = 1) (hb : d332889 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309477, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91162 q ha hb
    | true =>
      simp only [d309477, d332889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91163 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309478 q = 1) (hb : d332890 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309478, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309478, d332890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309479 q = 1) (hb : d333267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309479, d333267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309480 q = 1) (hb : d333268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309480, d333268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309484 q = 1) (hb : d333270 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309484, d333270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91164 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44681 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309485 q = 1) (hb : d333271 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309485, d333271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309486 q = 1) (hb : d333272 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309486, d333272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309487 q = 1) (hb : d333273 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309487, d333273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309488 q = 1) (hb : d333274 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309488, d333274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309494 q = 1) (hb : d333281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309494, d333281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91165 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44820 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309495 q = 1) (hb : d333282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309495, d333282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309496 q = 1) (hb : d333283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309496, d333283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309497 q = 1) (hb : d333284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309497, d333284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309498 q = 1) (hb : d333285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309498, d333285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309499 q = 1) (hb : d333286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309499, d333286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91167 (p : Pattern) (ha : d309505 p = 1) (hb : d333292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309500 q = 1) (hb : d333287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309500, d333287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91166 q ha hb
  have h2 (q : Pattern) (ha : d309501 q = 1) (hb : d333288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309501, d333288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309502 q = 1) (hb : d333289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309502, d333289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309503 q = 1) (hb : d333290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309503, d333290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309504 q = 1) (hb : d333291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309504, d333291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309505 q = 1) (hb : d333292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309505, d333292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91168 (p : Pattern) (ha : d309809 p = 1) (hb : d331425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309805 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309805, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309806 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309806, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309807 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309807, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309808 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309808, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309809 q = 1) (hb : d331425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309809, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91169 (p : Pattern) (ha : d309814 p = 1) (hb : d331432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331361 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309805 q = 1) (hb : d331421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309805, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309806 q = 1) (hb : d331422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309806, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309807 q = 1) (hb : d331423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309807, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309808 q = 1) (hb : d331424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309808, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42445 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309810 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309810, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309811 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309811, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309812 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309812, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309813 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309813, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309814 q = 1) (hb : d331432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309814, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91170 (p : Pattern) (ha : d309821 p = 1) (hb : d333130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331368 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309810 q = 1) (hb : d331428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309810, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309811 q = 1) (hb : d331429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309811, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309819 q = 1) (hb : d331430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309819, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309820 q = 1) (hb : d331431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309820, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309821 q = 1) (hb : d333130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309821, d333130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91171 (p : Pattern) (ha : d309831 p = 1) (hb : d333140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309827 q = 1) (hb : d333136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309827, d333136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309828 q = 1) (hb : d333137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309828, d333137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309829 q = 1) (hb : d333138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309829, d333138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309830 q = 1) (hb : d333139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309830, d333139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309831 q = 1) (hb : d333140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309831, d333140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91172 (p : Pattern) (ha : d309837 p = 1) (hb : d333146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309815 q = 1) (hb : d331433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91168 q ha hb
    | true =>
      simp only [d309815, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91169 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309816 q = 1) (hb : d331434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309816, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309817 q = 1) (hb : d333128 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309817, d333128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309818 q = 1) (hb : d333129 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309818, d333129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309822 q = 1) (hb : d333131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309822, d333131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91170 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309823 q = 1) (hb : d333132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309823, d333132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309824 q = 1) (hb : d333133 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309824, d333133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309825 q = 1) (hb : d333134 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309825, d333134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309826 q = 1) (hb : d333135 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309826, d333135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309832 q = 1) (hb : d333141 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309832, d333141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91171 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309833 q = 1) (hb : d333142 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309833, d333142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309834 q = 1) (hb : d333143 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309834, d333143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309835 q = 1) (hb : d333144 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309835, d333144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309836 q = 1) (hb : d333145 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309836, d333145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309837 q = 1) (hb : d333146 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309837, d333146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91173 (p : Pattern) (ha : d309843 p = 1) (hb : d333152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d309800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80535 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d309801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d309802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d309804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309838 q = 1) (hb : d333147 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309838, d333147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91172 q ha hb
  have h8 (q : Pattern) (ha : d309839 q = 1) (hb : d333148 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309839, d333148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309840 q = 1) (hb : d333149 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309840, d333149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309841 q = 1) (hb : d333150 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309841, d333150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309842 q = 1) (hb : d333151 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309842, d333151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309843 q = 1) (hb : d333152 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d309843, d333152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro91174 (p : Pattern) (ha : d309848 p = 1) (hb : d331595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309844 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309844, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309845 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309845, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309846 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309846, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309847 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309847, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309848 q = 1) (hb : d331595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309848, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91175 (p : Pattern) (ha : d309853 p = 1) (hb : d331605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331590 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309844 q = 1) (hb : d331591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309844, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309845 q = 1) (hb : d331592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309845, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309846 q = 1) (hb : d331593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309846, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309847 q = 1) (hb : d331594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309847, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42705 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309849 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309849, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309850 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309850, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309851 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309851, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309852 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309852, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309853 q = 1) (hb : d331605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309853, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91176 (p : Pattern) (ha : d309860 p = 1) (hb : d333155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309849 q = 1) (hb : d331601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309849, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309850 q = 1) (hb : d331602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309850, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309858 q = 1) (hb : d331603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309858, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309859 q = 1) (hb : d331604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309859, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309860 q = 1) (hb : d333155 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309860, d333155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91177 (p : Pattern) (ha : d309870 p = 1) (hb : d333166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333161 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309866 q = 1) (hb : d333162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309866, d333162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309867 q = 1) (hb : d333163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309867, d333163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309868 q = 1) (hb : d333164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309868, d333164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309869 q = 1) (hb : d333165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309869, d333165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309870 q = 1) (hb : d333166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309870, d333166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91178 (p : Pattern) (ha : d309876 p = 1) (hb : d333172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309854 q = 1) (hb : d331606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91174 q ha hb
    | true =>
      simp only [d309854, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91175 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309855 q = 1) (hb : d331607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309855, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309856 q = 1) (hb : d333153 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309856, d333153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309857 q = 1) (hb : d333154 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309857, d333154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309861 q = 1) (hb : d333156 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309861, d333156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91176 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42746 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309862 q = 1) (hb : d333157 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309862, d333157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309863 q = 1) (hb : d333158 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309863, d333158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309864 q = 1) (hb : d333159 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309864, d333159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309865 q = 1) (hb : d333160 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309865, d333160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309871 q = 1) (hb : d333167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309871, d333167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91177 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309872 q = 1) (hb : d333168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309872, d333168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309873 q = 1) (hb : d333169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309873, d333169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309874 q = 1) (hb : d333170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309874, d333170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309875 q = 1) (hb : d333171 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309875, d333171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309876 q = 1) (hb : d333172 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309876, d333172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91179 (p : Pattern) (ha : d309882 p = 1) (hb : d333178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309877 q = 1) (hb : d333173 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309877, d333173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91178 q ha hb
  have h2 (q : Pattern) (ha : d309878 q = 1) (hb : d333174 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309878, d333174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309879 q = 1) (hb : d333175 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309879, d333175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309880 q = 1) (hb : d333176 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309880, d333176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309881 q = 1) (hb : d333177 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309881, d333177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309882 q = 1) (hb : d333178 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309882, d333178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91180 (p : Pattern) (ha : d309888 p = 1) (hb : d331845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309884 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309884, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309885 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309885, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309886 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309886, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309887 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309887, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309888 q = 1) (hb : d331845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309888, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91181 (p : Pattern) (ha : d309893 p = 1) (hb : d331855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d331840 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309884 q = 1) (hb : d331841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309884, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309885 q = 1) (hb : d331842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309885, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309886 q = 1) (hb : d331843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309886, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309887 q = 1) (hb : d331844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309887, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43091 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309889 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309889, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309890 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309890, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309891 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309891, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309892 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309892, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309893 q = 1) (hb : d331855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309893, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91182 (p : Pattern) (ha : d309900 p = 1) (hb : d333182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309889 q = 1) (hb : d331851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309889, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309890 q = 1) (hb : d331852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309890, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309898 q = 1) (hb : d331853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309898, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309899 q = 1) (hb : d331854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309899, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309900 q = 1) (hb : d333182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309900, d333182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91183 (p : Pattern) (ha : d309910 p = 1) (hb : d333193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309906 q = 1) (hb : d333189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309906, d333189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309907 q = 1) (hb : d333190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309907, d333190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309908 q = 1) (hb : d333191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309908, d333191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309909 q = 1) (hb : d333192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309909, d333192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309910 q = 1) (hb : d333193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309910, d333193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91184 (p : Pattern) (ha : d309916 p = 1) (hb : d333199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309894 q = 1) (hb : d331856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91180 q ha hb
    | true =>
      simp only [d309894, d331856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91181 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309895 q = 1) (hb : d331857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309895, d331857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309896 q = 1) (hb : d333180 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309896, d333180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309897 q = 1) (hb : d333181 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309897, d333181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309901 q = 1) (hb : d333183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309901, d333183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91182 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309902 q = 1) (hb : d333184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309902, d333184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309903 q = 1) (hb : d333185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309903, d333185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309904 q = 1) (hb : d333186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309904, d333186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309905 q = 1) (hb : d333187 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309905, d333187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309911 q = 1) (hb : d333194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309911, d333194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91183 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309912 q = 1) (hb : d333195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309912, d333195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309913 q = 1) (hb : d333196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309913, d333196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309914 q = 1) (hb : d333197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309914, d333197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309915 q = 1) (hb : d333198 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309915, d333198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309916 q = 1) (hb : d333199 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309916, d333199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91185 (p : Pattern) (ha : d309922 p = 1) (hb : d333205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309917 q = 1) (hb : d333200 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309917, d333200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91184 q ha hb
  have h2 (q : Pattern) (ha : d309918 q = 1) (hb : d333201 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309918, d333201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309919 q = 1) (hb : d333202 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309919, d333202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309920 q = 1) (hb : d333203 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309920, d333203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309921 q = 1) (hb : d333204 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309921, d333204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309922 q = 1) (hb : d333205 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309922, d333205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91186 (p : Pattern) (ha : d309929 p = 1) (hb : d332173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309925 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309925, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309926 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309926, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309927 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309927, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309928 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309928, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309929 q = 1) (hb : d332173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309929, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309929, d332173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91187 (p : Pattern) (ha : d309934 p = 1) (hb : d332183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309925 q = 1) (hb : d332169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309925, d332169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309926 q = 1) (hb : d332170 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309926, d332170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309927 q = 1) (hb : d332171 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309927, d332171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309928 q = 1) (hb : d332172 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309928, d332172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309930 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309930, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309931 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309931, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309932 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309932, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309932, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309933 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309933, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309933, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309934 q = 1) (hb : d332183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309934, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309934, d332183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91188 (p : Pattern) (ha : d309941 p = 1) (hb : d333210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309930 q = 1) (hb : d332179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309930, d332179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309931 q = 1) (hb : d332180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309931, d332180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309939 q = 1) (hb : d332181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309939, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309939, d332181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309940 q = 1) (hb : d332182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309940, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309940, d332182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309941 q = 1) (hb : d333210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309941, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309941, d333210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91189 (p : Pattern) (ha : d309951 p = 1) (hb : d333221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309947 q = 1) (hb : d333217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309947, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309947, d333217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309948 q = 1) (hb : d333218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309948, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309948, d333218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309949 q = 1) (hb : d333219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309949, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309949, d333219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309950 q = 1) (hb : d333220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309950, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309950, d333220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309951 q = 1) (hb : d333221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309951, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309951, d333221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91190 (p : Pattern) (ha : d309957 p = 1) (hb : d333227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309935 q = 1) (hb : d332184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309935, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91186 q ha hb
    | true =>
      simp only [d309935, d332184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91187 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309936 q = 1) (hb : d332185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309936, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309936, d332185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309937 q = 1) (hb : d333208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309937, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309937, d333208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309938 q = 1) (hb : d333209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309938, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309938, d333209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309942 q = 1) (hb : d333211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309942, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309942, d333211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91188 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43646 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309943 q = 1) (hb : d333212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309943, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309943, d333212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309944 q = 1) (hb : d333213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309944, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309944, d333213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309945 q = 1) (hb : d333214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309945, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309945, d333214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309946 q = 1) (hb : d333215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309946, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309946, d333215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309952 q = 1) (hb : d333222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309952, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309952, d333222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91189 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309953 q = 1) (hb : d333223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309953, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309953, d333223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309954 q = 1) (hb : d333224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309954, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309954, d333224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309955 q = 1) (hb : d333225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309955, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309955, d333225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309956 q = 1) (hb : d333226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309956, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309956, d333226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309957 q = 1) (hb : d333227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309957, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309957, d333227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91191 (p : Pattern) (ha : d309963 p = 1) (hb : d333233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309958 q = 1) (hb : d333228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309958, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309958, d333228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91190 q ha hb
  have h2 (q : Pattern) (ha : d309959 q = 1) (hb : d333229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309959, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309959, d333229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309960 q = 1) (hb : d333230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309960, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309960, d333230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309961 q = 1) (hb : d333231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309961, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309961, d333231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309962 q = 1) (hb : d333232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309962, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309962, d333232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309963 q = 1) (hb : d333233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309963, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309963, d333233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91192 (p : Pattern) (ha : d309971 p = 1) (hb : d332545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309967 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309967, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309968 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309968, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309969 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309969, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309970 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309970, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309971 q = 1) (hb : d332545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309971, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309971, d332545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro91193 (p : Pattern) (ha : d309976 p = 1) (hb : d332555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d332540 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309967 q = 1) (hb : d332541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309967, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309967, d332541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309968 q = 1) (hb : d332542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309968, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309968, d332542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309969 q = 1) (hb : d332543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309969, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309969, d332543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309970 q = 1) (hb : d332544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309970, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309970, d332544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44196 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309972 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309972, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309973 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309973, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309974 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309974, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309974, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309975 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309975, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309975, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309976 q = 1) (hb : d332555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309976, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309976, d332555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91194 (p : Pattern) (ha : d309983 p = 1) (hb : d333239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d332550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309972 q = 1) (hb : d332551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309972, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309972, d332551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309973 q = 1) (hb : d332552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309973, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309973, d332552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309981 q = 1) (hb : d332553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309981, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309981, d332553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309982 q = 1) (hb : d332554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309982, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309982, d332554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309983 q = 1) (hb : d333239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309983, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309983, d333239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91195 (p : Pattern) (ha : d309993 p = 1) (hb : d333250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d333245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309989 q = 1) (hb : d333246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309989, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309989, d333246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309990 q = 1) (hb : d333247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309990, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309990, d333247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309991 q = 1) (hb : d333248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309991, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309991, d333248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309992 q = 1) (hb : d333249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309992, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309992, d333249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309993 q = 1) (hb : d333250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309993, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309993, d333250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91196 (p : Pattern) (ha : d309999 p = 1) (hb : d333256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309977 q = 1) (hb : d332556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309977, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91192 q ha hb
    | true =>
      simp only [d309977, d332556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91193 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309978 q = 1) (hb : d332557 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309978, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309978, d332557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309979 q = 1) (hb : d333237 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309979, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309979, d333237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309980 q = 1) (hb : d333238 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309980, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309980, d333238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309984 q = 1) (hb : d333240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309984, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309984, d333240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91194 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309985 q = 1) (hb : d333241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309985, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309985, d333241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309986 q = 1) (hb : d333242 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309986, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309986, d333242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309987 q = 1) (hb : d333243 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309987, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309987, d333243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309988 q = 1) (hb : d333244 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309988, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309988, d333244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309994 q = 1) (hb : d333251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309994, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309994, d333251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91195 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309995 q = 1) (hb : d333252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309995, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309995, d333252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309996 q = 1) (hb : d333253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309996, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309996, d333253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309997 q = 1) (hb : d333254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309997, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309997, d333254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309998 q = 1) (hb : d333255 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309998, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309998, d333255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309999 q = 1) (hb : d333256 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309999, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309999, d333256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91197 (p : Pattern) (ha : d310005 p = 1) (hb : d333262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310000 q = 1) (hb : d333257 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d310000, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310000, d333257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91196 q ha hb
  have h2 (q : Pattern) (ha : d310001 q = 1) (hb : d333258 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d310001, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310001, d333258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310002 q = 1) (hb : d333259 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d310002, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310002, d333259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310003 q = 1) (hb : d333260 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d310003, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310003, d333260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310004 q = 1) (hb : d333261 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d310004, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310004, d333261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310005 q = 1) (hb : d333262 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d310005, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310005, d333262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91198 (p : Pattern) (ha : d310011 p = 1) (hb : d333298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d309883 q = 1) (hb : d333179 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91173 q ha hb
    | true =>
      simp only [d309883, d333179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91179 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309923 q = 1) (hb : d333206 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309923, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309923, d333206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91185 q ha hb
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d333207 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309924, d333207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309964 q = 1) (hb : d333234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309964, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309964, d333234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91191 q ha hb
  have h5 (q : Pattern) (ha : d309965 q = 1) (hb : d333235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309965, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309965, d333235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309966 q = 1) (hb : d333236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d333236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310006 q = 1) (hb : d333263 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d310006, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310006, d333263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91197 q ha hb
  have h8 (q : Pattern) (ha : d310007 q = 1) (hb : d333264 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d310007, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310007, d333264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310008 q = 1) (hb : d333265 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d310008, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310008, d333265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310009 q = 1) (hb : d333266 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310009, d333266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309506 q = 1) (hb : d333293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309506, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309506, d333293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91167 q ha hb
  have h12 (q : Pattern) (ha : d309507 q = 1) (hb : d333294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309507, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309507, d333294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309508 q = 1) (hb : d333295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309508, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309508, d333295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309509 q = 1) (hb : d333296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309509, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309509, d333296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d310010 q = 1) (hb : d333297 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d310010, d333297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d310011 q = 1) (hb : d333298 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d310011, d333298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro91199 (p : Pattern) (ha : d310017 p = 1) (hb : d333304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d333299 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91198 q ha hb
    | true =>
      simp only [d310012, d333299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d333300 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d333300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d333301 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d333301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d333302 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d333302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d333303 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d333303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d333304 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d333304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91200 (p : Pattern) (ha : d310023 p = 1) (hb : d333310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d333305 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91199 q ha hb
    | true =>
      simp only [d310018, d333305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d333306 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d333306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d333307 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d333307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d333308 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d333308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d333309 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d333309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310023 q = 1) (hb : d333310 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d333310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91201 (p : Pattern) (ha : d310029 p = 1) (hb : d333316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d333311 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91200 q ha hb
    | true =>
      simp only [d310024, d333311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d333312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d333312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d333313 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d333313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d333314 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d333314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d333315 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d333315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d333316 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d333316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91202 (p : Pattern) (ha : d310035 p = 1) (hb : d333322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d333317 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91201 q ha hb
    | true =>
      simp only [d310030, d333317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d333318 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d333318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d333319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d333319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d333320 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d333320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d333321 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d333321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d333322 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d333322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91203 (p : Pattern) (ha : d310041 p = 1) (hb : d333328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d333323 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91202 q ha hb
    | true =>
      simp only [d310036, d333323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d333324 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d333324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d333325 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d333325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d333326 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d333326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d333327 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d333327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d333328 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d333328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91204 (p : Pattern) (ha : d310047 p = 1) (hb : d333334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d333329 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91203 q ha hb
    | true =>
      simp only [d310042, d333329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d333330 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d333330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d333331 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d333331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d333332 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d333332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d333333 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d333333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d333334 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d333334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91205 (p : Pattern) (ha : d310053 p = 1) (hb : d333340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d333335 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91204 q ha hb
    | true =>
      simp only [d310048, d333335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d333336 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d333336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d333337 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d333337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d333338 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d333338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d333339 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d333339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d333340 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d333340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91206 (p : Pattern) (ha : d38819 p = 1) (hb : d236581 p = 1) : d28891 p = 1 := by
  have h0 (q : Pattern) (ha : d28887 q = 1) (hb : d236581 q = 1) : d28887 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d38813 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d38814 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d38815 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38816 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28888 q = 1) (hb : d236581 q = 1) : d28888 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d38817 q = 1) (hb : d236581 q = 1) : d28889 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38817, d28889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38817, d28889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38818 q = 1) (hb : d236581 q = 1) : d28890 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38818, d28890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38818, d28890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d38819 q = 1) (hb : d236581 q = 1) : d28891 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38819, d28891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38819, d28891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91207 (p : Pattern) (ha : d38826 p = 1) (hb : d236581 p = 1) : d28896 p = 1 := by
  have h0 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d38814 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38815 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38816 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28742 q = 1) (hb : d236581 q = 1) : d28742 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d38824 q = 1) (hb : d236581 q = 1) : d28743 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38824, d28743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38824, d28743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38825 q = 1) (hb : d236581 q = 1) : d28744 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38825, d28744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38825, d28744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d23229 q = 1) (hb : d236581 q = 1) : d23229 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d38826 q = 1) (hb : d236581 q = 1) : d28896 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38826, d28896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38826, d28896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91208 (p : Pattern) (ha : d38835 p = 1) (hb : d236581 p = 1) : d29093 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38814 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d38815 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d38832 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38832, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38832, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d236581 q = 1) : d9796 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d38833 q = 1) (hb : d236581 q = 1) : d29088 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38833, d29088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38833, d29088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38834 q = 1) (hb : d236581 q = 1) : d29089 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38834, d29089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38834, d29089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1115 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1116 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d236581 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1117 q = 1) (hb : d236581 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21 q = 1) (hb : d236581 q = 1) : d21 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1118 q = 1) (hb : d236581 q = 1) : d29091 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1119 q = 1) (hb : d236581 q = 1) : d29092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d38835 q = 1) (hb : d236581 q = 1) : d29093 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38835, d29093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38835, d29093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro91209 (p : Pattern) (ha : d38841 p = 1) (hb : d236581 p = 1) : d29099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38820 q = 1) (hb : d236581 q = 1) : d28892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38820, d28892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91206 q ha hb
    | true =>
      simp only [d38820, d28892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38821 q = 1) (hb : d236581 q = 1) : d28893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38821, d28893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38821, d28893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38822 q = 1) (hb : d236581 q = 1) : d28894 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38822, d28894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38822, d28894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38823 q = 1) (hb : d236581 q = 1) : d28895 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38823, d28895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38823, d28895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38827 q = 1) (hb : d236581 q = 1) : d28897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38827, d28897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91207 q ha hb
    | true =>
      simp only [d38827, d28897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38828 q = 1) (hb : d236581 q = 1) : d28898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38828, d28898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38828, d28898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38829 q = 1) (hb : d236581 q = 1) : d28899 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38829, d28899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38829, d28899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38830 q = 1) (hb : d236581 q = 1) : d28900 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38830, d28900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38830, d28900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d38831 q = 1) (hb : d236581 q = 1) : d28901 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38831, d28901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38831, d28901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23425 q = 1) (hb : d236581 q = 1) : d23425 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d38836 q = 1) (hb : d236581 q = 1) : d29094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91208 q ha hb
    | true =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d38837 q = 1) (hb : d236581 q = 1) : d29095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d38838 q = 1) (hb : d236581 q = 1) : d29096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d38839 q = 1) (hb : d236581 q = 1) : d29097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d38840 q = 1) (hb : d236581 q = 1) : d29098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38840, d29098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38840, d29098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d38841 q = 1) (hb : d236581 q = 1) : d29099 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38841, d29099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38841, d29099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro91210 (p : Pattern) (ha : d38845 p = 1) (hb : d236581 p = 1) : d28745 p = 1 := by
  have h0 (q : Pattern) (ha : d532 q = 1) (hb : d236581 q = 1) : d532 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d38814 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38815 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38816 q = 1) (hb : d236581 q = 1) : d533 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38816, d533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28742 q = 1) (hb : d236581 q = 1) : d28742 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d38824 q = 1) (hb : d236581 q = 1) : d28743 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38824, d28743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38824, d28743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38825 q = 1) (hb : d236581 q = 1) : d28744 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38825, d28744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38825, d28744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d132 q = 1) : d132 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1104 q = 1) (hb : d236581 q = 1) : d133 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d1105 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d38842 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38842, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38842, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d135 q = 1) (hb : d236581 q = 1) : d135 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d38843 q = 1) (hb : d236581 q = 1) : d316 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38843, d316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d38843, d316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d38844 q = 1) (hb : d236581 q = 1) : d317 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38844, d317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d38844, d317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d38845 q = 1) (hb : d236581 q = 1) : d28745 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38845, d28745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38845, d28745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro91211 (p : Pattern) (ha : d38850 p = 1) (hb : d236581 p = 1) : d29100 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d312 q = 1) : d312 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38814 q = 1) (hb : d236581 q = 1) : d313 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d38814, d236581, d313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d38815 q = 1) (hb : d236581 q = 1) : d314 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38815, d314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d132 q = 1) : d132 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1104 q = 1) (hb : d236581 q = 1) : d133 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1104, d236581, d133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1105 q = 1) (hb : d236581 q = 1) : d134 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1105, d134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d38842 q = 1) (hb : d236581 q = 1) : d315 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38842, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38842, d315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d135 q = 1) (hb : d236581 q = 1) : d135 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d38843 q = 1) (hb : d236581 q = 1) : d316 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d38843, d316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38843, d316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d38844 q = 1) (hb : d236581 q = 1) : d317 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d38844, d317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d38844, d317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1115 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h15 (q : Pattern) (ha : d1116 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d236581 q = 1) : d20 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1117 q = 1) (hb : d236581 q = 1) : d29090 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1117, d29090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21 q = 1) (hb : d236581 q = 1) : d21 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d1118 q = 1) (hb : d236581 q = 1) : d29091 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1118, d29091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1119 q = 1) (hb : d236581 q = 1) : d29092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1119, d29092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h21 (q : Pattern) (ha : d38850 q = 1) (hb : d236581 q = 1) : d29100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d38850, d29100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d38850, d29100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro91212 (p : Pattern) (ha : d38857 p = 1) (hb : d236581 p = 1) : d29107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38846 q = 1) (hb : d236581 q = 1) : d28746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38846, d28746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91210 q ha hb
    | true =>
      simp only [d38846, d28746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38847 q = 1) (hb : d236581 q = 1) : d28747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38847, d28747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38847, d28747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38848 q = 1) (hb : d236581 q = 1) : d28748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38848, d28748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38848, d28748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38849 q = 1) (hb : d236581 q = 1) : d28749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38849, d28749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38849, d28749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38851 q = 1) (hb : d236581 q = 1) : d29101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
    | true =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38852 q = 1) (hb : d236581 q = 1) : d29102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38853 q = 1) (hb : d236581 q = 1) : d29103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38854 q = 1) (hb : d236581 q = 1) : d29104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d38855 q = 1) (hb : d236581 q = 1) : d29105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38855, d29105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38855, d29105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38836 q = 1) (hb : d236581 q = 1) : d29094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91208 q ha hb
    | true =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d38837 q = 1) (hb : d236581 q = 1) : d29095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d38838 q = 1) (hb : d236581 q = 1) : d29096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d38839 q = 1) (hb : d236581 q = 1) : d29097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d38856 q = 1) (hb : d236581 q = 1) : d29106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38856, d29106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d38856, d29106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d38857 q = 1) (hb : d236581 q = 1) : d29107 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38857, d29107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38857, d29107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91213 (p : Pattern) (ha : d9843 p = 1) (hb : d236581 p = 1) : d29114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d236581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1116 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1132 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d236581 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9841 q = 1) (hb : d236581 q = 1) : d29112 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9841, d29112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9842 q = 1) (hb : d236581 q = 1) : d29113 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9842, d29113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d9843 q = 1) (hb : d236581 q = 1) : d29114 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9843, d29114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h9 p ha hb
theorem andIntro91214 (p : Pattern) (ha : d38862 p = 1) (hb : d236581 p = 1) : d29120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38851 q = 1) (hb : d236581 q = 1) : d29101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
    | true =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38852 q = 1) (hb : d236581 q = 1) : d29102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38853 q = 1) (hb : d236581 q = 1) : d29103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38854 q = 1) (hb : d236581 q = 1) : d29104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38861 q = 1) (hb : d236581 q = 1) : d29111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38861, d29111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38861, d29111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d236581 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91213 q ha hb
    | true =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d236581 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d236581 q = 1) : d29117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d29117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d236581 q = 1) : d29118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d29118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d236581 q = 1) : d29119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d29119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d38862 q = 1) (hb : d236581 q = 1) : d29120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38862, d29120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38862, d29120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91215 (p : Pattern) (ha : d38869 p = 1) (hb : d236581 p = 1) : d29127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38858 q = 1) (hb : d236581 q = 1) : d29108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91209 q ha hb
    | true =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
  have h2 (q : Pattern) (ha : d38859 q = 1) (hb : d236581 q = 1) : d29109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38860 q = 1) (hb : d236581 q = 1) : d29110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38863 q = 1) (hb : d236581 q = 1) : d29121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
    | true =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91214 q ha hb
  have h5 (q : Pattern) (ha : d38864 q = 1) (hb : d236581 q = 1) : d29122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38865 q = 1) (hb : d236581 q = 1) : d29123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38866 q = 1) (hb : d236581 q = 1) : d29124 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38867 q = 1) (hb : d236581 q = 1) : d29125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38867, d29125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38867, d29125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d38868 q = 1) (hb : d236581 q = 1) : d29126 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d38868, d29126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38868, d29126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38869 q = 1) (hb : d236581 q = 1) : d29127 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d38869, d29127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d38869, d29127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro91216 (p : Pattern) (ha : d38873 p = 1) (hb : d236581 p = 1) : d29131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38863 q = 1) (hb : d236581 q = 1) : d29121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
    | true =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91214 q ha hb
  have h2 (q : Pattern) (ha : d38864 q = 1) (hb : d236581 q = 1) : d29122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38865 q = 1) (hb : d236581 q = 1) : d29123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38867 q = 1) (hb : d236581 q = 1) : d29125 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38867, d29125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38867, d29125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38872 q = 1) (hb : d236581 q = 1) : d29130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d38872, d29130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38872, d29130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38873 q = 1) (hb : d236581 q = 1) : d29131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d38873, d29131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38873, d29131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91217 (p : Pattern) (ha : d38879 p = 1) (hb : d236581 p = 1) : d29137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38877 q = 1) (hb : d236581 q = 1) : d29135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38878 q = 1) (hb : d236581 q = 1) : d29136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38878, d29136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38878, d29136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38879 q = 1) (hb : d236581 q = 1) : d29137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38879, d29137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38879, d29137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91218 (p : Pattern) (ha : d38883 p = 1) (hb : d236581 p = 1) : d29141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38881 q = 1) (hb : d236581 q = 1) : d29139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38882 q = 1) (hb : d236581 q = 1) : d29140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38882, d29140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38882, d29140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38883 q = 1) (hb : d236581 q = 1) : d29141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38883, d29141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38883, d29141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91219 (p : Pattern) (ha : d38889 p = 1) (hb : d236581 p = 1) : d29147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38884 q = 1) (hb : d236581 q = 1) : d29142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91217 q ha hb
    | true =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91218 q ha hb
  have h2 (q : Pattern) (ha : d38885 q = 1) (hb : d236581 q = 1) : d29143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38886 q = 1) (hb : d236581 q = 1) : d29144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38887 q = 1) (hb : d236581 q = 1) : d29145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38888 q = 1) (hb : d236581 q = 1) : d29146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38889 q = 1) (hb : d236581 q = 1) : d29147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d38889, d29147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38889, d29147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91220 (p : Pattern) (ha : d38892 p = 1) (hb : d236581 p = 1) : d29150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38877 q = 1) (hb : d236581 q = 1) : d29135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38878 q = 1) (hb : d236581 q = 1) : d29136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38878, d29136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38878, d29136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38892 q = 1) (hb : d236581 q = 1) : d29150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38892, d29150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38892, d29150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91221 (p : Pattern) (ha : d38893 p = 1) (hb : d236581 p = 1) : d29151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38881 q = 1) (hb : d236581 q = 1) : d29139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38882 q = 1) (hb : d236581 q = 1) : d29140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38882, d29140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38882, d29140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38893 q = 1) (hb : d236581 q = 1) : d29151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38893, d29151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38893, d29151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91222 (p : Pattern) (ha : d38899 p = 1) (hb : d236581 p = 1) : d29157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38884 q = 1) (hb : d236581 q = 1) : d29142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91217 q ha hb
    | true =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91218 q ha hb
  have h2 (q : Pattern) (ha : d38885 q = 1) (hb : d236581 q = 1) : d29143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38886 q = 1) (hb : d236581 q = 1) : d29144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38887 q = 1) (hb : d236581 q = 1) : d29145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38888 q = 1) (hb : d236581 q = 1) : d29146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38894 q = 1) (hb : d236581 q = 1) : d29152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38894, d29152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91220 q ha hb
    | true =>
      simp only [d38894, d29152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91221 q ha hb
  have h7 (q : Pattern) (ha : d38895 q = 1) (hb : d236581 q = 1) : d29153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38895, d29153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38895, d29153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38896 q = 1) (hb : d236581 q = 1) : d29154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38896, d29154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38896, d29154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d38897 q = 1) (hb : d236581 q = 1) : d29155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38897, d29155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38897, d29155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38898 q = 1) (hb : d236581 q = 1) : d29156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38898, d29156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38898, d29156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38899 q = 1) (hb : d236581 q = 1) : d29157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d38899, d29157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38899, d29157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91223 (p : Pattern) (ha : d39059 p = 1) (hb : d236581 p = 1) : d29339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38884 q = 1) (hb : d236581 q = 1) : d29142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91217 q ha hb
    | true =>
      simp only [d38884, d29142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91218 q ha hb
  have h2 (q : Pattern) (ha : d38885 q = 1) (hb : d236581 q = 1) : d29143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38885, d29143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38886 q = 1) (hb : d236581 q = 1) : d29144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38886, d29144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38887 q = 1) (hb : d236581 q = 1) : d29145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38887, d29145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38888 q = 1) (hb : d236581 q = 1) : d29146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38888, d29146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39054 q = 1) (hb : d236581 q = 1) : d29334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39054, d29334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91218 q ha hb
    | true =>
      simp only [d39054, d29334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39055 q = 1) (hb : d236581 q = 1) : d29335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39055, d29335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39055, d29335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39056 q = 1) (hb : d236581 q = 1) : d29336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39056, d29336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39056, d29336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39057 q = 1) (hb : d236581 q = 1) : d29337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39057, d29337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39057, d29337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39058 q = 1) (hb : d236581 q = 1) : d29338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39058, d29338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39058, d29338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39059 q = 1) (hb : d236581 q = 1) : d29339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39059, d29339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39059, d29339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91224 (p : Pattern) (ha : d39065 p = 1) (hb : d236581 p = 1) : d29345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39054 q = 1) (hb : d236581 q = 1) : d29334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39054, d29334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91218 q ha hb
    | true =>
      simp only [d39054, d29334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39055 q = 1) (hb : d236581 q = 1) : d29335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39055, d29335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39055, d29335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39056 q = 1) (hb : d236581 q = 1) : d29336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39056, d29336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39056, d29336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39057 q = 1) (hb : d236581 q = 1) : d29337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39057, d29337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39057, d29337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39058 q = 1) (hb : d236581 q = 1) : d29338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39058, d29338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39058, d29338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39060 q = 1) (hb : d236581 q = 1) : d29340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39060, d29340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91221 q ha hb
    | true =>
      simp only [d39060, d29340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39061 q = 1) (hb : d236581 q = 1) : d29341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39061, d29341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39061, d29341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39062 q = 1) (hb : d236581 q = 1) : d29342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39062, d29342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39062, d29342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39063 q = 1) (hb : d236581 q = 1) : d29343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39063, d29343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39063, d29343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39064 q = 1) (hb : d236581 q = 1) : d29344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39064, d29344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39064, d29344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39065 q = 1) (hb : d236581 q = 1) : d29345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39065, d29345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39065, d29345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro91225 (p : Pattern) (ha : d39074 p = 1) (hb : d236581 p = 1) : d29354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39060 q = 1) (hb : d236581 q = 1) : d29340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39060, d29340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91221 q ha hb
    | true =>
      simp only [d39060, d29340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39061 q = 1) (hb : d236581 q = 1) : d29341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39061, d29341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39061, d29341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39062 q = 1) (hb : d236581 q = 1) : d29342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39062, d29342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39062, d29342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39063 q = 1) (hb : d236581 q = 1) : d29343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39063, d29343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39063, d29343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39064 q = 1) (hb : d236581 q = 1) : d29344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39064, d29344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39064, d29344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39074 q = 1) (hb : d236581 q = 1) : d29354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39074, d29354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39074, d29354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91226 (p : Pattern) (ha : d39113 p = 1) (hb : d236581 p = 1) : d29390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39104 q = 1) (hb : d236581 q = 1) : d28794 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39104, d28794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39104, d28794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91210 q ha hb
  have h2 (q : Pattern) (ha : d38846 q = 1) (hb : d236581 q = 1) : d28746 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38846, d28746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91210 q ha hb
    | true =>
      simp only [d38846, d28746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39105 q = 1) (hb : d236581 q = 1) : d28795 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39105, d28795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39105, d28795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38847 q = 1) (hb : d236581 q = 1) : d28747 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38847, d28747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38847, d28747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39106 q = 1) (hb : d236581 q = 1) : d28796 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39106, d28796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39106, d28796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39107 q = 1) (hb : d236581 q = 1) : d28797 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39107, d28797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39107, d28797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39108 q = 1) (hb : d236581 q = 1) : d29385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39108, d29385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39108, d29385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
  have h8 (q : Pattern) (ha : d38851 q = 1) (hb : d236581 q = 1) : d29101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
    | true =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d39109 q = 1) (hb : d236581 q = 1) : d29386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39109, d29386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39109, d29386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38852 q = 1) (hb : d236581 q = 1) : d29102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39110 q = 1) (hb : d236581 q = 1) : d29387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39110, d29387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d39110, d29387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d39111 q = 1) (hb : d236581 q = 1) : d29388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39111, d29388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d39111, d29388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d39112 q = 1) (hb : d236581 q = 1) : d29389 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39112, d29389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39112, d29389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d39089 q = 1) (hb : d236581 q = 1) : d29370 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39089, d29370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39089, d29370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91208 q ha hb
  have h15 (q : Pattern) (ha : d38836 q = 1) (hb : d236581 q = 1) : d29094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91208 q ha hb
    | true =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d39090 q = 1) (hb : d236581 q = 1) : d29371 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39090, d29371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d39090, d29371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d38837 q = 1) (hb : d236581 q = 1) : d29095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39091 q = 1) (hb : d236581 q = 1) : d29372 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39091, d29372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39091, d29372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39092 q = 1) (hb : d236581 q = 1) : d29373 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39092, d29373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d39092, d29373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d39098 q = 1) (hb : d236581 q = 1) : d29379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39098, d29379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d39098, d29379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d39113 q = 1) (hb : d236581 q = 1) : d29390 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39113, d29390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d39113, d29390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro91227 (p : Pattern) (ha : d39118 p = 1) (hb : d236581 p = 1) : d29400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39108 q = 1) (hb : d236581 q = 1) : d29385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d39108, d29385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39108, d29385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
  have h2 (q : Pattern) (ha : d38851 q = 1) (hb : d236581 q = 1) : d29101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
    | true =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d39109 q = 1) (hb : d236581 q = 1) : d29386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d39109, d29386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d39109, d29386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38852 q = 1) (hb : d236581 q = 1) : d29102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39110 q = 1) (hb : d236581 q = 1) : d29387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d39110, d29387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39110, d29387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39111 q = 1) (hb : d236581 q = 1) : d29388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d39111, d29388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39111, d29388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d39117 q = 1) (hb : d236581 q = 1) : d29394 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d39117, d29394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d39117, d29394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d236581 q = 1) : d29395 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d29395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91213 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d236581 q = 1) : d29115 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91213 q ha hb
    | true =>
      simp only [d9844, d29115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d236581 q = 1) : d29396 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d29396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d236581 q = 1) : d29116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d29116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d236581 q = 1) : d29397 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d29397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d236581 q = 1) : d29398 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d29398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d236581 q = 1) : d29399 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d29399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d39118 q = 1) (hb : d236581 q = 1) : d29400 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39118, d29400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39118, d29400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91228 (p : Pattern) (ha : d39137 p = 1) (hb : d236581 p = 1) : d29419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39119 q = 1) (hb : d236581 q = 1) : d29401 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39119, d29401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91226 q ha hb
    | true =>
      simp only [d39119, d29401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91227 q ha hb
  have h2 (q : Pattern) (ha : d39120 q = 1) (hb : d236581 q = 1) : d29402 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39120, d29402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39120, d29402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39121 q = 1) (hb : d236581 q = 1) : d29403 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39121, d29403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39121, d29403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d39127 q = 1) (hb : d236581 q = 1) : d29409 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39127, d29409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39127, d29409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39136 q = 1) (hb : d236581 q = 1) : d29418 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39136, d29418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39136, d29418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39137 q = 1) (hb : d236581 q = 1) : d29419 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39137, d29419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39137, d29419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91229 (p : Pattern) (ha : d39222 p = 1) (hb : d236581 p = 1) : d29505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39138 q = 1) (hb : d236581 q = 1) : d29420 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39138, d29420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91228 q ha hb
    | true =>
      simp only [d39138, d29420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39139 q = 1) (hb : d236581 q = 1) : d29421 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39139, d29421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39139, d29421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39219 q = 1) (hb : d236581 q = 1) : d29502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39219, d29502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39219, d29502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39220 q = 1) (hb : d236581 q = 1) : d29503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39220, d29503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39220, d29503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39221 q = 1) (hb : d236581 q = 1) : d29504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39221, d29504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39221, d29504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39222 q = 1) (hb : d236581 q = 1) : d29505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39222, d29505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39222, d29505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91230 (p : Pattern) (ha : d39228 p = 1) (hb : d236581 p = 1) : d29511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39223 q = 1) (hb : d236581 q = 1) : d29506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39223, d29506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91229 q ha hb
    | true =>
      simp only [d39223, d29506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39224 q = 1) (hb : d236581 q = 1) : d29507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39224, d29507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39224, d29507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39225 q = 1) (hb : d236581 q = 1) : d29508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39225, d29508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39225, d29508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39226 q = 1) (hb : d236581 q = 1) : d29509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39226, d29509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39226, d29509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d39227 q = 1) (hb : d236581 q = 1) : d29510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d39227, d29510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39227, d29510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39228 q = 1) (hb : d236581 q = 1) : d29511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d39228, d29511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39228, d29511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91231 (p : Pattern) (ha : d38904 p = 1) (hb : d236581 p = 1) : d29162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38877 q = 1) (hb : d236581 q = 1) : d29135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38903 q = 1) (hb : d236581 q = 1) : d29161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38903, d29161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38903, d29161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38904 q = 1) (hb : d236581 q = 1) : d29162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38904, d29162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38904, d29162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91232 (p : Pattern) (ha : d38906 p = 1) (hb : d236581 p = 1) : d29164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38881 q = 1) (hb : d236581 q = 1) : d29139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38905 q = 1) (hb : d236581 q = 1) : d29163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38905, d29163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38905, d29163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38906 q = 1) (hb : d236581 q = 1) : d29164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38906, d29164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38906, d29164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91233 (p : Pattern) (ha : d38913 p = 1) (hb : d236581 p = 1) : d29171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38911 q = 1) (hb : d236581 q = 1) : d29169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38911, d29169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38911, d29169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38912 q = 1) (hb : d236581 q = 1) : d29170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38912, d29170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38912, d29170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38913 q = 1) (hb : d236581 q = 1) : d29171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38913, d29171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38913, d29171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91234 (p : Pattern) (ha : d38916 p = 1) (hb : d236581 p = 1) : d29174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38914 q = 1) (hb : d236581 q = 1) : d29172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38914, d29172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38914, d29172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38915 q = 1) (hb : d236581 q = 1) : d29173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38915, d29173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38915, d29173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d38916 q = 1) (hb : d236581 q = 1) : d29174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38916, d29174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38916, d29174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91235 (p : Pattern) (ha : d38923 p = 1) (hb : d236581 p = 1) : d29196 p = 1 := by
  have h0 (q : Pattern) (ha : d23425 q = 1) (hb : d236581 q = 1) : d23425 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38836 q = 1) (hb : d236581 q = 1) : d29094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91208 q ha hb
    | true =>
      simp only [d38836, d29094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38837 q = 1) (hb : d236581 q = 1) : d29095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38837, d29095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d38838 q = 1) (hb : d236581 q = 1) : d29096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38838, d29096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38839 q = 1) (hb : d236581 q = 1) : d29097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38839, d29097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d38840 q = 1) (hb : d236581 q = 1) : d29098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38840, d29098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38840, d29098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38856 q = 1) (hb : d236581 q = 1) : d29106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38856, d29106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38856, d29106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d38923 q = 1) (hb : d236581 q = 1) : d29196 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d38923, d29196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38923, d29196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91236 (p : Pattern) (ha : d38929 p = 1) (hb : d236581 p = 1) : d29202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29192 q = 1) (hb : d236581 q = 1) : d29192 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38920 q = 1) (hb : d236581 q = 1) : d29193 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38920, d29193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38920, d29193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91209 q ha hb
  have h3 (q : Pattern) (ha : d38921 q = 1) (hb : d236581 q = 1) : d29194 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38921, d29194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38921, d29194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38922 q = 1) (hb : d236581 q = 1) : d29195 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38922, d29195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38922, d29195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38924 q = 1) (hb : d236581 q = 1) : d29197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38924, d29197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91209 q ha hb
    | true =>
      simp only [d38924, d29197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91235 q ha hb
  have h6 (q : Pattern) (ha : d38925 q = 1) (hb : d236581 q = 1) : d29198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38925, d29198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38925, d29198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38926 q = 1) (hb : d236581 q = 1) : d29199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38926, d29199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38926, d29199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38927 q = 1) (hb : d236581 q = 1) : d29200 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38927, d29200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38927, d29200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d38858 q = 1) (hb : d236581 q = 1) : d29108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91209 q ha hb
    | true =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
  have h10 (q : Pattern) (ha : d38859 q = 1) (hb : d236581 q = 1) : d29109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38860 q = 1) (hb : d236581 q = 1) : d29110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d38863 q = 1) (hb : d236581 q = 1) : d29121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
    | true =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91214 q ha hb
  have h13 (q : Pattern) (ha : d38864 q = 1) (hb : d236581 q = 1) : d29122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d38865 q = 1) (hb : d236581 q = 1) : d29123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d38866 q = 1) (hb : d236581 q = 1) : d29124 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d38928 q = 1) (hb : d236581 q = 1) : d29201 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d38928, d29201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38928, d29201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d38929 q = 1) (hb : d236581 q = 1) : d29202 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d38929, d29202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d38929, d29202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro91237 (p : Pattern) (ha : d38935 p = 1) (hb : d236581 p = 1) : d29208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38930 q = 1) (hb : d236581 q = 1) : d29203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38930, d29203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91236 q ha hb
    | true =>
      simp only [d38930, d29203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38931 q = 1) (hb : d236581 q = 1) : d29204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38931, d29204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38931, d29204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38932 q = 1) (hb : d236581 q = 1) : d29205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38932, d29205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38932, d29205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38933 q = 1) (hb : d236581 q = 1) : d29206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38933, d29206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38933, d29206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38934 q = 1) (hb : d236581 q = 1) : d29207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38934, d29207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38934, d29207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38935 q = 1) (hb : d236581 q = 1) : d29208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d38935, d29208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38935, d29208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro91238 (p : Pattern) (ha : d39010 p = 1) (hb : d236581 p = 1) : d29290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38851 q = 1) (hb : d236581 q = 1) : d29101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91211 q ha hb
    | true =>
      simp only [d38851, d29101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38852 q = 1) (hb : d236581 q = 1) : d29102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38852, d29102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38853 q = 1) (hb : d236581 q = 1) : d29103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38853, d29103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38854 q = 1) (hb : d236581 q = 1) : d29104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38854, d29104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38861 q = 1) (hb : d236581 q = 1) : d29111 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38861, d29111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38861, d29111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39010 q = 1) (hb : d236581 q = 1) : d29290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d39010, d29290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39010, d29290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91239 (p : Pattern) (ha : d39016 p = 1) (hb : d236581 p = 1) : d29296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38858 q = 1) (hb : d236581 q = 1) : d29108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91209 q ha hb
    | true =>
      simp only [d38858, d29108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
  have h2 (q : Pattern) (ha : d38859 q = 1) (hb : d236581 q = 1) : d29109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38859, d29109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38860 q = 1) (hb : d236581 q = 1) : d29110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38860, d29110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38863 q = 1) (hb : d236581 q = 1) : d29121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
    | true =>
      simp only [d38863, d29121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91214 q ha hb
  have h5 (q : Pattern) (ha : d38864 q = 1) (hb : d236581 q = 1) : d29122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38864, d29122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38865 q = 1) (hb : d236581 q = 1) : d29123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38865, d29123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38866 q = 1) (hb : d236581 q = 1) : d29124 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38866, d29124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39011 q = 1) (hb : d236581 q = 1) : d29291 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d39011, d29291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91212 q ha hb
    | true =>
      simp only [d39011, d29291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91238 q ha hb
  have h9 (q : Pattern) (ha : d39012 q = 1) (hb : d236581 q = 1) : d29292 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d39012, d29292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39012, d29292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d39013 q = 1) (hb : d236581 q = 1) : d29293 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d39013, d29293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39013, d29293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d39014 q = 1) (hb : d236581 q = 1) : d29294 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d39014, d29294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39014, d29294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d39015 q = 1) (hb : d236581 q = 1) : d29295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d39015, d29295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39015, d29295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d39016 q = 1) (hb : d236581 q = 1) : d29296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d39016, d29296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d39016, d29296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro91240 (p : Pattern) (ha : d39022 p = 1) (hb : d236581 p = 1) : d29302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39017 q = 1) (hb : d236581 q = 1) : d29297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39017, d29297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91239 q ha hb
    | true =>
      simp only [d39017, d29297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39018 q = 1) (hb : d236581 q = 1) : d29298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39018, d29298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39018, d29298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39019 q = 1) (hb : d236581 q = 1) : d29299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39019, d29299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39019, d29299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39020 q = 1) (hb : d236581 q = 1) : d29300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39020, d29300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39020, d29300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39021 q = 1) (hb : d236581 q = 1) : d29301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39021, d29301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39021, d29301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39022 q = 1) (hb : d236581 q = 1) : d29302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39022, d29302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39022, d29302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro91241 (p : Pattern) (ha : d236581 p = 1) (hb : d280938 p = 1) : d238956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38907 q = 1) (hb : d236581 q = 1) : d29165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38907, d29165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91231 q ha hb
    | true =>
      simp only [d38907, d29165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91232 q ha hb
  have h2 (q : Pattern) (ha : d38908 q = 1) (hb : d236581 q = 1) : d29166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38908, d29166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38908, d29166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38909 q = 1) (hb : d236581 q = 1) : d29167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38909, d29167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38909, d29167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38910 q = 1) (hb : d236581 q = 1) : d29168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38910, d29168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38910, d29168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38917 q = 1) (hb : d236581 q = 1) : d29175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38917, d29175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91233 q ha hb
    | true =>
      simp only [d38917, d29175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91234 q ha hb
  have h6 (q : Pattern) (ha : d38918 q = 1) (hb : d236581 q = 1) : d29176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38918, d29176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38918, d29176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38919 q = 1) (hb : d236581 q = 1) : d29177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38919, d29177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38919, d29177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38936 q = 1) (hb : d236581 q = 1) : d29209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38936, d29209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91237 q ha hb
    | true =>
      simp only [d38936, d29209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91217 q ha hb
  have h9 (q : Pattern) (ha : d236581 q = 1) (hb : d280934 q = 1) : d238952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280934, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d280934, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d39023 q = 1) (hb : d236581 q = 1) : d29303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39023, d29303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91240 q ha hb
    | true =>
      simp only [d39023, d29303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39024 q = 1) (hb : d236581 q = 1) : d29304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39024, d29304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39024, d29304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d236581 q = 1) (hb : d280935 q = 1) : d238953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d280935, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d280935, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d236581 q = 1) (hb : d280936 q = 1) : d238954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d280936, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d280936, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d236581 q = 1) (hb : d280937 q = 1) : d238955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d280937, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d280937, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d236581 q = 1) (hb : d280938 q = 1) : d238956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d280938, d238956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d280938, d238956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro91242 (p : Pattern) (ha : d39029 p = 1) (hb : d236581 p = 1) : d29309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38877 q = 1) (hb : d236581 q = 1) : d29135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38877, d29135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38903 q = 1) (hb : d236581 q = 1) : d29161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38903, d29161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38903, d29161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d39029 q = 1) (hb : d236581 q = 1) : d29309 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39029, d29309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39029, d29309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91243 (p : Pattern) (ha : d39030 p = 1) (hb : d236581 p = 1) : d29310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38881 q = 1) (hb : d236581 q = 1) : d29139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38881, d29139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38905 q = 1) (hb : d236581 q = 1) : d29163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38905, d29163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38905, d29163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d39030 q = 1) (hb : d236581 q = 1) : d29310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39030, d29310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39030, d29310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91244 (p : Pattern) (ha : d39035 p = 1) (hb : d236581 p = 1) : d29315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38876 q = 1) (hb : d236581 q = 1) : d29134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38876, d29134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38911 q = 1) (hb : d236581 q = 1) : d29169 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38911, d29169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38911, d29169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38912 q = 1) (hb : d236581 q = 1) : d29170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38912, d29170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38912, d29170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39035 q = 1) (hb : d236581 q = 1) : d29315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39035, d29315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39035, d29315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91245 (p : Pattern) (ha : d39036 p = 1) (hb : d236581 p = 1) : d29316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38874 q = 1) (hb : d236581 q = 1) : d29132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91216 q ha hb
    | true =>
      simp only [d38874, d29132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38875 q = 1) (hb : d236581 q = 1) : d29133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38875, d29133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38880 q = 1) (hb : d236581 q = 1) : d29138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38880, d29138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38914 q = 1) (hb : d236581 q = 1) : d29172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38914, d29172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38914, d29172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38915 q = 1) (hb : d236581 q = 1) : d29173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38915, d29173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d38915, d29173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39036 q = 1) (hb : d236581 q = 1) : d29316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39036, d29316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39036, d29316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91246 (p : Pattern) (ha : d39040 p = 1) (hb : d236581 p = 1) : d29320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38930 q = 1) (hb : d236581 q = 1) : d29203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38930, d29203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91236 q ha hb
    | true =>
      simp only [d38930, d29203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38931 q = 1) (hb : d236581 q = 1) : d29204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38931, d29204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38931, d29204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38870 q = 1) (hb : d236581 q = 1) : d29128 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91215 q ha hb
    | true =>
      simp only [d38870, d29128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38871 q = 1) (hb : d236581 q = 1) : d29129 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38871, d29129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38932 q = 1) (hb : d236581 q = 1) : d29205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d38932, d29205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38932, d29205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38933 q = 1) (hb : d236581 q = 1) : d29206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d38933, d29206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38933, d29206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38934 q = 1) (hb : d236581 q = 1) : d29207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d38934, d29207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38934, d29207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d39040 q = 1) (hb : d236581 q = 1) : d29320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39040, d29320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d39040, d29320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro91247 (p : Pattern) (ha : d39046 p = 1) (hb : d236581 p = 1) : d29326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39017 q = 1) (hb : d236581 q = 1) : d29297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d39017, d29297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91239 q ha hb
    | true =>
      simp only [d39017, d29297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d39018 q = 1) (hb : d236581 q = 1) : d29298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d39018, d29298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39018, d29298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39019 q = 1) (hb : d236581 q = 1) : d29299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39019, d29299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39019, d29299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39020 q = 1) (hb : d236581 q = 1) : d29300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d39020, d29300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39020, d29300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d39021 q = 1) (hb : d236581 q = 1) : d29301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d39021, d29301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39021, d29301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d39046 q = 1) (hb : d236581 q = 1) : d29326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d39046, d29326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d39046, d29326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro91248 (p : Pattern) (ha : d236581 p = 1) (hb : d280943 p = 1) : d238961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38907 q = 1) (hb : d236581 q = 1) : d29165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38907, d29165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91231 q ha hb
    | true =>
      simp only [d38907, d29165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91232 q ha hb
  have h2 (q : Pattern) (ha : d38908 q = 1) (hb : d236581 q = 1) : d29166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38908, d29166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38908, d29166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38909 q = 1) (hb : d236581 q = 1) : d29167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38909, d29167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38909, d29167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38910 q = 1) (hb : d236581 q = 1) : d29168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38910, d29168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38910, d29168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38917 q = 1) (hb : d236581 q = 1) : d29175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38917, d29175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91233 q ha hb
    | true =>
      simp only [d38917, d29175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91234 q ha hb
  have h6 (q : Pattern) (ha : d38918 q = 1) (hb : d236581 q = 1) : d29176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38918, d29176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38918, d29176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38919 q = 1) (hb : d236581 q = 1) : d29177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38919, d29177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38919, d29177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38936 q = 1) (hb : d236581 q = 1) : d29209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38936, d29209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91237 q ha hb
    | true =>
      simp only [d38936, d29209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91217 q ha hb
  have h9 (q : Pattern) (ha : d236581 q = 1) (hb : d280934 q = 1) : d238952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280934, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d280934, d238952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d39023 q = 1) (hb : d236581 q = 1) : d29303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39023, d29303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91240 q ha hb
    | true =>
      simp only [d39023, d29303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d39024 q = 1) (hb : d236581 q = 1) : d29304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39024, d29304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d39024, d29304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d236581 q = 1) (hb : d280935 q = 1) : d238953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d280935, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d280935, d238953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d236581 q = 1) (hb : d280936 q = 1) : d238954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d280936, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d280936, d238954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d236581 q = 1) (hb : d280937 q = 1) : d238955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d280937, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d280937, d238955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d39031 q = 1) (hb : d236581 q = 1) : d29311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39031, d29311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91242 q ha hb
    | true =>
      simp only [d39031, d29311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91243 q ha hb
  have h16 (q : Pattern) (ha : d39032 q = 1) (hb : d236581 q = 1) : d29312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39032, d29312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39032, d29312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d39033 q = 1) (hb : d236581 q = 1) : d29313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39033, d29313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d39033, d29313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d39034 q = 1) (hb : d236581 q = 1) : d29314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d39034, d29314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39034, d29314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d39037 q = 1) (hb : d236581 q = 1) : d29317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39037, d29317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91244 q ha hb
    | true =>
      simp only [d39037, d29317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91245 q ha hb
  have h20 (q : Pattern) (ha : d39038 q = 1) (hb : d236581 q = 1) : d29318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39038, d29318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39038, d29318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d39039 q = 1) (hb : d236581 q = 1) : d29319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d39039, d29319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d39039, d29319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d39041 q = 1) (hb : d236581 q = 1) : d29321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39041, d29321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91246 q ha hb
    | true =>
      simp only [d39041, d29321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91220 q ha hb
  have h23 (q : Pattern) (ha : d236581 q = 1) (hb : d280939 q = 1) : d238957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280939, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d280939, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d39047 q = 1) (hb : d236581 q = 1) : d29327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39047, d29327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91247 q ha hb
    | true =>
      simp only [d39047, d29327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d39048 q = 1) (hb : d236581 q = 1) : d29328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39048, d29328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d39048, d29328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d236581 q = 1) (hb : d280940 q = 1) : d238958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d280940, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d280940, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d236581 q = 1) (hb : d280941 q = 1) : d238959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d280941, d238959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d280941, d238959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d236581 q = 1) (hb : d280942 q = 1) : d238960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d280942, d238960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d280942, d238960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d236581 q = 1) (hb : d280943 q = 1) : d238961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d280943, d238961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d280943, d238961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro91249 (p : Pattern) (ha : d236581 p = 1) (hb : d280950 p = 1) : d238968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d39041 q = 1) (hb : d236581 q = 1) : d29321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39041, d29321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91246 q ha hb
    | true =>
      simp only [d39041, d29321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91220 q ha hb
  have h2 (q : Pattern) (ha : d236581 q = 1) (hb : d280939 q = 1) : d238957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280939, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d280939, d238957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d39047 q = 1) (hb : d236581 q = 1) : d29327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d39047, d29327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91247 q ha hb
    | true =>
      simp only [d39047, d29327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d39048 q = 1) (hb : d236581 q = 1) : d29328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d39048, d29328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39048, d29328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d236581 q = 1) (hb : d280940 q = 1) : d238958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d280940, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280940, d238958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236581 q = 1) (hb : d280948 q = 1) : d238966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d280948, d238966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d280948, d238966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236581 q = 1) (hb : d280949 q = 1) : d238967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d280949, d238967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d280949, d238967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236581 q = 1) (hb : d280950 q = 1) : d238968 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d280950, d238968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d280950, d238968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
