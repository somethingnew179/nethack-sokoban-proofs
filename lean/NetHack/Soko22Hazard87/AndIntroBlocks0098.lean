import NetHack.Soko22Hazard87.AndIntroBlocks0097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro24500 (p : Pattern) (ha : d137625 p = 1) (hb : d138828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137623 q = 1) (hb : d138826 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137623, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137623, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137624 q = 1) (hb : d138827 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137624, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137624, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137625 q = 1) (hb : d138828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137625, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137625, d138828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24501 (p : Pattern) (ha : d137633 p = 1) (hb : d138837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53015 q = 1) (hb : d138832 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12839 q hb ha
  have h3 (q : Pattern) (ha : d137629 q = 1) (hb : d138833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137629, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137629, d138833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137630 q = 1) (hb : d138834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137630, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137630, d138834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53027 q = 1) (hb : d138772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q hb ha
  have h7 (q : Pattern) (ha : d137571 q = 1) (hb : d138773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137572 q = 1) (hb : d138774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137631 q = 1) (hb : d138835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137631, d138835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137631, d138835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53029 q = 1) (hb : d138775 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q hb ha
  have h12 (q : Pattern) (ha : d137573 q = 1) (hb : d138776 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137574 q = 1) (hb : d138777 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137575 q = 1) (hb : d138778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137632 q = 1) (hb : d138836 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137632, d138836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137632, d138836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137633 q = 1) (hb : d138837 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137633, d138837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137633, d138837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24502 (p : Pattern) (ha : d137639 p = 1) (hb : d138843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137634 q = 1) (hb : d138838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137634, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24501 q ha hb
    | true =>
      simp only [d137634, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137635 q = 1) (hb : d138839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137635, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137635, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137636 q = 1) (hb : d138840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137636, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137636, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137637 q = 1) (hb : d138841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137637, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137637, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137638 q = 1) (hb : d138842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137638, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137638, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137639 q = 1) (hb : d138843 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137639, d138843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137639, d138843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24503 (p : Pattern) (ha : d5636 p = 1) (hb : d74360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5630 q = 1) (hb : d74356 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5631 q = 1) (hb : d74357 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5632 q = 1) (hb : d74358 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5632, d74358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5633 q = 1) (hb : d74359 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5633, d74359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5634 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5634, d74360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5636 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24504 (p : Pattern) (ha : d137646 p = 1) (hb : d138851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53027 q = 1) (hb : d138772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q hb ha
  have h3 (q : Pattern) (ha : d137571 q = 1) (hb : d138773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137571, d138773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137572 q = 1) (hb : d138774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137572, d138774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53029 q = 1) (hb : d138775 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q hb ha
  have h7 (q : Pattern) (ha : d137573 q = 1) (hb : d138776 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137573, d138776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137574 q = 1) (hb : d138777 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137574, d138777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137575 q = 1) (hb : d138778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137575, d138778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74360 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74360 q = 1) (hb : d138846 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24503 q hb ha
  have h12 (q : Pattern) (ha : d137642 q = 1) (hb : d138847 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137642, d138847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137642, d138847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137643 q = 1) (hb : d138848 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137643, d138848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137643, d138848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137644 q = 1) (hb : d138849 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137644, d138849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137644, d138849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137645 q = 1) (hb : d138850 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137645, d138850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137645, d138850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137646 q = 1) (hb : d138851 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137646, d138851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137646, d138851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24505 (p : Pattern) (ha : d137652 p = 1) (hb : d138857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137647 q = 1) (hb : d138852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137647, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24504 q ha hb
    | true =>
      simp only [d137647, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137648 q = 1) (hb : d138853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137648, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137648, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137649 q = 1) (hb : d138854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137649, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137649, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137650 q = 1) (hb : d138855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137650, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137650, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137651 q = 1) (hb : d138856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137651, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137651, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137652 q = 1) (hb : d138857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137652, d138857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137652, d138857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24506 (p : Pattern) (ha : d137658 p = 1) (hb : d138863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137616 q = 1) (hb : d138819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137616, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24497 q ha hb
    | true =>
      simp only [d137616, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24498 q ha hb
  have h2 (q : Pattern) (ha : d137617 q = 1) (hb : d138820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137617, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137617, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137618 q = 1) (hb : d138821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137618, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137618, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137619 q = 1) (hb : d138822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137619, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137619, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137626 q = 1) (hb : d138829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137626, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24499 q ha hb
    | true =>
      simp only [d137626, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24500 q ha hb
  have h6 (q : Pattern) (ha : d137627 q = 1) (hb : d138830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137627, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137627, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137628 q = 1) (hb : d138831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137628, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137628, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137640 q = 1) (hb : d138844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137640, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24502 q ha hb
    | true =>
      simp only [d137640, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137641 q = 1) (hb : d138845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137641, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137641, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137653 q = 1) (hb : d138858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137653, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24505 q ha hb
    | true =>
      simp only [d137653, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137654 q = 1) (hb : d138859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137654, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137654, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137655 q = 1) (hb : d138860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137655, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137655, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137656 q = 1) (hb : d138861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137656, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137656, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137657 q = 1) (hb : d138862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137657, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137657, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137658 q = 1) (hb : d138863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137658, d138863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137658, d138863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24507 (p : Pattern) (ha : d137659 p = 1) (hb : d138864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137586 q = 1) (hb : d138789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137586, d138789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137612 q = 1) (hb : d138815 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137612, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137612, d138815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137659 q = 1) (hb : d138864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137659, d138864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137659, d138864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24508 (p : Pattern) (ha : d137660 p = 1) (hb : d138865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137590 q = 1) (hb : d138793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137590, d138793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137614 q = 1) (hb : d138817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137614, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137614, d138817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137660 q = 1) (hb : d138865 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137660, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137660, d138865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24509 (p : Pattern) (ha : d137665 p = 1) (hb : d138870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137585 q = 1) (hb : d138788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137585, d138788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137620 q = 1) (hb : d138823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137620, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137620, d138823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137621 q = 1) (hb : d138824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137621, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137621, d138824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137665 q = 1) (hb : d138870 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137665, d138870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137665, d138870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24510 (p : Pattern) (ha : d137666 p = 1) (hb : d138871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137583 q = 1) (hb : d138786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24490 q ha hb
    | true =>
      simp only [d137583, d138786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137584 q = 1) (hb : d138787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137584, d138787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137589 q = 1) (hb : d138792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137589, d138792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137623 q = 1) (hb : d138826 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137623, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137623, d138826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137624 q = 1) (hb : d138827 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137624, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137624, d138827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137666 q = 1) (hb : d138871 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137666, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137666, d138871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24511 (p : Pattern) (ha : d137670 p = 1) (hb : d138875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137634 q = 1) (hb : d138838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137634, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24501 q ha hb
    | true =>
      simp only [d137634, d138838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137635 q = 1) (hb : d138839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137635, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137635, d138839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137579 q = 1) (hb : d138782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24489 q ha hb
    | true =>
      simp only [d137579, d138782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137580 q = 1) (hb : d138783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137580, d138783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137636 q = 1) (hb : d138840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137636, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137636, d138840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137637 q = 1) (hb : d138841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137637, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137637, d138841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137638 q = 1) (hb : d138842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137638, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137638, d138842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137670 q = 1) (hb : d138875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137670, d138875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137670, d138875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24512 (p : Pattern) (ha : d137673 p = 1) (hb : d138878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137647 q = 1) (hb : d138852 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137647, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24504 q ha hb
    | true =>
      simp only [d137647, d138852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137648 q = 1) (hb : d138853 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137648, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137648, d138853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137649 q = 1) (hb : d138854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137649, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137649, d138854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137650 q = 1) (hb : d138855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137650, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137650, d138855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137651 q = 1) (hb : d138856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137651, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137651, d138856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137673 q = 1) (hb : d138878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137673, d138878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137673, d138878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24513 (p : Pattern) (ha : d137679 p = 1) (hb : d138884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137616 q = 1) (hb : d138819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137616, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24497 q ha hb
    | true =>
      simp only [d137616, d138819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24498 q ha hb
  have h2 (q : Pattern) (ha : d137617 q = 1) (hb : d138820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137617, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137617, d138820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137618 q = 1) (hb : d138821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137618, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137618, d138821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137619 q = 1) (hb : d138822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137619, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137619, d138822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137626 q = 1) (hb : d138829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137626, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24499 q ha hb
    | true =>
      simp only [d137626, d138829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24500 q ha hb
  have h6 (q : Pattern) (ha : d137627 q = 1) (hb : d138830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137627, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137627, d138830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137628 q = 1) (hb : d138831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137628, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137628, d138831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137640 q = 1) (hb : d138844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137640, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24502 q ha hb
    | true =>
      simp only [d137640, d138844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137641 q = 1) (hb : d138845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137641, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137641, d138845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137653 q = 1) (hb : d138858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137653, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24505 q ha hb
    | true =>
      simp only [d137653, d138858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137654 q = 1) (hb : d138859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137654, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137654, d138859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137655 q = 1) (hb : d138860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137655, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137655, d138860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137656 q = 1) (hb : d138861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137656, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137656, d138861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137657 q = 1) (hb : d138862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137657, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137657, d138862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137661 q = 1) (hb : d138866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137661, d138866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24507 q ha hb
    | true =>
      simp only [d137661, d138866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24508 q ha hb
  have h17 (q : Pattern) (ha : d137662 q = 1) (hb : d138867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137662, d138867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137662, d138867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137663 q = 1) (hb : d138868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137663, d138868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137663, d138868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137664 q = 1) (hb : d138869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137664, d138869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137664, d138869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137667 q = 1) (hb : d138872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137667, d138872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24509 q ha hb
    | true =>
      simp only [d137667, d138872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24510 q ha hb
  have h21 (q : Pattern) (ha : d137668 q = 1) (hb : d138873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137668, d138873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137668, d138873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137669 q = 1) (hb : d138874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137669, d138874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137669, d138874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137671 q = 1) (hb : d138876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137671, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24511 q ha hb
    | true =>
      simp only [d137671, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24494 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d137603 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d137672 q = 1) (hb : d138877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137672, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d137672, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137674 q = 1) (hb : d138879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137674, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24512 q ha hb
    | true =>
      simp only [d137674, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137675 q = 1) (hb : d138880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137675, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137675, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d137676 q = 1) (hb : d138881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137676, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d137676, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d137677 q = 1) (hb : d138882 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137677, d138882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d137677, d138882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d137678 q = 1) (hb : d138883 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137678, d138883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137678, d138883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d137679 q = 1) (hb : d138884 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137679, d138884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137679, d138884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24514 (p : Pattern) (ha : d137686 p = 1) (hb : d138891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137593 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
    | true =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
  have h2 (q : Pattern) (ha : d137594 q = 1) (hb : d138797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137594, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137595 q = 1) (hb : d138798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137595, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137596 q = 1) (hb : d138799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137596, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137597 q = 1) (hb : d138800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137597, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137681 q = 1) (hb : d138886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137681, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
    | true =>
      simp only [d137681, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137682 q = 1) (hb : d138887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137682, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137682, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137683 q = 1) (hb : d138888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137683, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137683, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137684 q = 1) (hb : d138889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137684, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137684, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137685 q = 1) (hb : d138890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137685, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137685, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137686 q = 1) (hb : d138891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137686, d138891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137686, d138891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24515 (p : Pattern) (ha : d137692 p = 1) (hb : d138897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137681 q = 1) (hb : d138886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137681, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
    | true =>
      simp only [d137681, d138886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137682 q = 1) (hb : d138887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137682, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137682, d138887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137683 q = 1) (hb : d138888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137683, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137683, d138888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137684 q = 1) (hb : d138889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137684, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137684, d138889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137685 q = 1) (hb : d138890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137685, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137685, d138890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137687 q = 1) (hb : d138892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137687, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24495 q ha hb
    | true =>
      simp only [d137687, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137688 q = 1) (hb : d138893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137688, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137688, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137689 q = 1) (hb : d138894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137689, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137689, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137690 q = 1) (hb : d138895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137690, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137690, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137691 q = 1) (hb : d138896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137691, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137691, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137692 q = 1) (hb : d138897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137692, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137692, d138897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24516 (p : Pattern) (ha : d137699 p = 1) (hb : d138904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137671 q = 1) (hb : d138876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137671, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24511 q ha hb
    | true =>
      simp only [d137671, d138876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24494 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137672 q = 1) (hb : d138877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137672, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137672, d138877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137674 q = 1) (hb : d138879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137674, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24512 q ha hb
    | true =>
      simp only [d137674, d138879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137675 q = 1) (hb : d138880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137675, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137675, d138880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137676 q = 1) (hb : d138881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137676, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137676, d138881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137697 q = 1) (hb : d138902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137697, d138902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137697, d138902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137698 q = 1) (hb : d138903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137698, d138903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137698, d138903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137699 q = 1) (hb : d138904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137699, d138904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137699, d138904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24517 (p : Pattern) (ha : d137701 p = 1) (hb : d138906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137687 q = 1) (hb : d138892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137687, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24495 q ha hb
    | true =>
      simp only [d137687, d138892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137688 q = 1) (hb : d138893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137688, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137688, d138893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137689 q = 1) (hb : d138894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137689, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137689, d138894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137690 q = 1) (hb : d138895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137690, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137690, d138895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137691 q = 1) (hb : d138896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137691, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137691, d138896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137701 q = 1) (hb : d138906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137701, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137701, d138906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24518 (p : Pattern) (ha : d137716 p = 1) (hb : d138924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53192 q = 1) (hb : d138912 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12855 q hb ha
  have h3 (q : Pattern) (ha : d137707 q = 1) (hb : d138913 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137707, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137707, d138913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137708 q = 1) (hb : d138914 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137708, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137708, d138914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53198 q = 1) (hb : d138915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q hb ha
  have h7 (q : Pattern) (ha : d137709 q = 1) (hb : d138916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137710 q = 1) (hb : d138917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137711 q = 1) (hb : d138918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137711, d138918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137711, d138918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53203 q = 1) (hb : d138919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q hb ha
  have h12 (q : Pattern) (ha : d137712 q = 1) (hb : d138920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137713 q = 1) (hb : d138921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137714 q = 1) (hb : d138922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137715 q = 1) (hb : d138923 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137715, d138923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137715, d138923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137716 q = 1) (hb : d138924 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137716, d138924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137716, d138924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24519 (p : Pattern) (ha : d137721 p = 1) (hb : d138929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53198 q = 1) (hb : d138915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q hb ha
  have h3 (q : Pattern) (ha : d137709 q = 1) (hb : d138916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137710 q = 1) (hb : d138917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53203 q = 1) (hb : d138919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q hb ha
  have h7 (q : Pattern) (ha : d137712 q = 1) (hb : d138920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137713 q = 1) (hb : d138921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137714 q = 1) (hb : d138922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137719 q = 1) (hb : d138927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137719, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137719, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137720 q = 1) (hb : d138928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137720, d138928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137720, d138928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137721 q = 1) (hb : d138929 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137721, d138929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137721, d138929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24520 (p : Pattern) (ha : d137727 p = 1) (hb : d138935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137717 q = 1) (hb : d138925 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137717, d138925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24518 q ha hb
    | true =>
      simp only [d137717, d138925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137718 q = 1) (hb : d138926 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137718, d138926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137718, d138926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137722 q = 1) (hb : d138930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137722, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24519 q ha hb
    | true =>
      simp only [d137722, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137723 q = 1) (hb : d138931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137723, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137723, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137724 q = 1) (hb : d138932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137724, d138932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137724, d138932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137725 q = 1) (hb : d138933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137725, d138933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137725, d138933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137726 q = 1) (hb : d138934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137726, d138934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137726, d138934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137727 q = 1) (hb : d138935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137727, d138935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137727, d138935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24521 (p : Pattern) (ha : d137729 p = 1) (hb : d138937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53203 q = 1) (hb : d138919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q hb ha
  have h3 (q : Pattern) (ha : d137712 q = 1) (hb : d138920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137713 q = 1) (hb : d138921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137719 q = 1) (hb : d138927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137719, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137719, d138927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137728 q = 1) (hb : d138936 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137728, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137728, d138936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137729 q = 1) (hb : d138937 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137729, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137729, d138937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24522 (p : Pattern) (ha : d137735 p = 1) (hb : d138943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137722 q = 1) (hb : d138930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137722, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24519 q ha hb
    | true =>
      simp only [d137722, d138930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137723 q = 1) (hb : d138931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137723, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137723, d138931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137730 q = 1) (hb : d138938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137730, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24521 q ha hb
    | true =>
      simp only [d137730, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137731 q = 1) (hb : d138939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137731, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137731, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137732 q = 1) (hb : d138940 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137732, d138940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137732, d138940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137733 q = 1) (hb : d138941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137733, d138941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137733, d138941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137734 q = 1) (hb : d138942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137734, d138942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137734, d138942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137735 q = 1) (hb : d138943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137735, d138943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137735, d138943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24523 (p : Pattern) (ha : d5680 p = 1) (hb : d74404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5674 q = 1) (hb : d74400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5674, d74400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
  have h2 (q : Pattern) (ha : d5630 q = 1) (hb : d74356 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9291 q ha hb
    | true =>
      simp only [d5630, d74356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5675 q = 1) (hb : d74401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5675, d74401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5631 q = 1) (hb : d74357 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5631, d74357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5676 q = 1) (hb : d74402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5676, d74402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5677 q = 1) (hb : d74403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5677, d74403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5678 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5678, d74404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5680 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24524 (p : Pattern) (ha : d137747 p = 1) (hb : d138951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53198 q = 1) (hb : d138915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q hb ha
  have h3 (q : Pattern) (ha : d137709 q = 1) (hb : d138916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137709, d138916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137710 q = 1) (hb : d138917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137710, d138917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53203 q = 1) (hb : d138919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q hb ha
  have h7 (q : Pattern) (ha : d137712 q = 1) (hb : d138920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137712, d138920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137713 q = 1) (hb : d138921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137713, d138921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137714 q = 1) (hb : d138922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137714, d138922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74404 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74404 q = 1) (hb : d138946 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24523 q hb ha
  have h12 (q : Pattern) (ha : d137743 q = 1) (hb : d138947 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137743, d138947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137743, d138947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137744 q = 1) (hb : d138948 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137744, d138948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137744, d138948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137745 q = 1) (hb : d138949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137745, d138949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137745, d138949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137746 q = 1) (hb : d138950 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137746, d138950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137746, d138950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137747 q = 1) (hb : d138951 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137747, d138951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137747, d138951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24525 (p : Pattern) (ha : d137753 p = 1) (hb : d138957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137748 q = 1) (hb : d138952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137748, d138952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24524 q ha hb
    | true =>
      simp only [d137748, d138952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137749 q = 1) (hb : d138953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137749, d138953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137749, d138953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137750 q = 1) (hb : d138954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137750, d138954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137750, d138954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137751 q = 1) (hb : d138955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137751, d138955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137751, d138955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137752 q = 1) (hb : d138956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137752, d138956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137752, d138956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137753 q = 1) (hb : d138957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137753, d138957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137753, d138957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24526 (p : Pattern) (ha : d137759 p = 1) (hb : d138963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137736 q = 1) (hb : d138944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137736, d138944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24520 q ha hb
    | true =>
      simp only [d137736, d138944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24522 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137742 q = 1) (hb : d138945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137742, d138945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137742, d138945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137754 q = 1) (hb : d138958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137754, d138958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24525 q ha hb
    | true =>
      simp only [d137754, d138958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137755 q = 1) (hb : d138959 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137755, d138959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137755, d138959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137756 q = 1) (hb : d138960 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137756, d138960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137756, d138960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137757 q = 1) (hb : d138961 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137757, d138961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137757, d138961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137758 q = 1) (hb : d138962 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137758, d138962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137758, d138962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137759 q = 1) (hb : d138963 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137759, d138963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137759, d138963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24527 (p : Pattern) (ha : d137740 p = 1) (hb : d138968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137730 q = 1) (hb : d138938 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137730, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24521 q ha hb
    | true =>
      simp only [d137730, d138938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137731 q = 1) (hb : d138939 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137731, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137731, d138939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137737 q = 1) (hb : d138965 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137737, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137737, d138965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137738 q = 1) (hb : d138966 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137738, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137738, d138966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137739 q = 1) (hb : d138967 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137739, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137739, d138967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137740 q = 1) (hb : d138968 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137740, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137740, d138968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24528 (p : Pattern) (ha : d137766 p = 1) (hb : d138974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137761 q = 1) (hb : d138969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137761, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24527 q ha hb
    | true =>
      simp only [d137761, d138969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137762 q = 1) (hb : d138970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137762, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137762, d138970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137763 q = 1) (hb : d138971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137763, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137763, d138971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137764 q = 1) (hb : d138972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137764, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137764, d138972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137765 q = 1) (hb : d138973 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137765, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137765, d138973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137766 q = 1) (hb : d138974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137766, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137766, d138974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24529 (p : Pattern) (ha : d137772 p = 1) (hb : d138980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137599 q = 1) (hb : d138802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137599, d138802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137599, d138802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24493 q ha hb
  have h2 (q : Pattern) (ha : d137600 q = 1) (hb : d138803 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137600, d138803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137600, d138803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137609 q = 1) (hb : d138812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137609, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24493 q ha hb
    | true =>
      simp only [d137609, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24496 q ha hb
  have h4 (q : Pattern) (ha : d137610 q = 1) (hb : d138813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137610, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137610, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137611 q = 1) (hb : d138814 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137611, d138814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137611, d138814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137680 q = 1) (hb : d138885 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137680, d138885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24506 q ha hb
    | true =>
      simp only [d137680, d138885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24513 q ha hb
  have h7 (q : Pattern) (ha : d137693 q = 1) (hb : d138898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137693, d138898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24514 q ha hb
    | true =>
      simp only [d137693, d138898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24515 q ha hb
  have h8 (q : Pattern) (ha : d137694 q = 1) (hb : d138899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137694, d138899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137694, d138899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137695 q = 1) (hb : d138900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137695, d138900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137695, d138900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d137696 q = 1) (hb : d138901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137696, d138901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137696, d138901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137700 q = 1) (hb : d138905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137700, d138905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137700, d138905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24516 q ha hb
  have h12 (q : Pattern) (ha : d137702 q = 1) (hb : d138907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137702, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137702, d138907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24517 q ha hb
  have h13 (q : Pattern) (ha : d137703 q = 1) (hb : d138908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137703, d138908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137703, d138908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137704 q = 1) (hb : d138909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137704, d138909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137704, d138909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137705 q = 1) (hb : d138910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137705, d138910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137705, d138910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d137706 q = 1) (hb : d138911 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137706, d138911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137706, d138911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137760 q = 1) (hb : d138964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137760, d138964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137760, d138964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24526 q ha hb
  have h18 (q : Pattern) (ha : d137767 q = 1) (hb : d138975 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137767, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137767, d138975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24528 q ha hb
  have h19 (q : Pattern) (ha : d137768 q = 1) (hb : d138976 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137768, d138976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137768, d138976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137769 q = 1) (hb : d138977 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137769, d138977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137769, d138977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137770 q = 1) (hb : d138978 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137770, d138978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d137770, d138978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d137771 q = 1) (hb : d138979 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137771, d138979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137771, d138979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137772 q = 1) (hb : d138980 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137772, d138980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137772, d138980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24530 (p : Pattern) (ha : d137778 p = 1) (hb : d138986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137773 q = 1) (hb : d138981 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137773, d138981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137773, d138981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24529 q ha hb
  have h2 (q : Pattern) (ha : d137774 q = 1) (hb : d138982 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137774, d138982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137774, d138982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137775 q = 1) (hb : d138983 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137775, d138983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137775, d138983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137776 q = 1) (hb : d138984 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137776, d138984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137776, d138984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137777 q = 1) (hb : d138985 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137777, d138985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137777, d138985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137778 q = 1) (hb : d138986 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137778, d138986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137778, d138986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24531 (p : Pattern) (ha : d137790 p = 1) (hb : d139000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53348 q = 1) (hb : d138991 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q hb ha
  have h3 (q : Pattern) (ha : d137783 q = 1) (hb : d138992 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137784 q = 1) (hb : d138993 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53350 q = 1) (hb : d138994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q hb ha
  have h7 (q : Pattern) (ha : d137785 q = 1) (hb : d138995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137786 q = 1) (hb : d138996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137787 q = 1) (hb : d138997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137788 q = 1) (hb : d138998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137788, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137788, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137789 q = 1) (hb : d138999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137789, d138999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137789, d138999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137790 q = 1) (hb : d139000 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137790, d139000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137790, d139000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24532 (p : Pattern) (ha : d137794 p = 1) (hb : d139004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53350 q = 1) (hb : d138994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q hb ha
  have h3 (q : Pattern) (ha : d137785 q = 1) (hb : d138995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137786 q = 1) (hb : d138996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137788 q = 1) (hb : d138998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137788, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137788, d138998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137793 q = 1) (hb : d139003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137793, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137793, d139003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137794 q = 1) (hb : d139004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137794, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137794, d139004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24533 (p : Pattern) (ha : d137800 p = 1) (hb : d139010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137798 q = 1) (hb : d139008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137799 q = 1) (hb : d139009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137799, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137799, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137800 q = 1) (hb : d139010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137800, d139010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137800, d139010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24534 (p : Pattern) (ha : d137804 p = 1) (hb : d139014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d139012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137803 q = 1) (hb : d139013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137803, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137803, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137804 q = 1) (hb : d139014 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137804, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137804, d139014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24535 (p : Pattern) (ha : d137810 p = 1) (hb : d139020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137805 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
    | true =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
  have h2 (q : Pattern) (ha : d137806 q = 1) (hb : d139016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137807 q = 1) (hb : d139017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137808 q = 1) (hb : d139018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137809 q = 1) (hb : d139019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137810 q = 1) (hb : d139020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137810, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137810, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24536 (p : Pattern) (ha : d137813 p = 1) (hb : d139023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137798 q = 1) (hb : d139008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137799 q = 1) (hb : d139009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137799, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137799, d139009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137813 q = 1) (hb : d139023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137813, d139023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137813, d139023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24537 (p : Pattern) (ha : d137814 p = 1) (hb : d139024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d139012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137803 q = 1) (hb : d139013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137803, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137803, d139013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137814 q = 1) (hb : d139024 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137814, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137814, d139024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24538 (p : Pattern) (ha : d137820 p = 1) (hb : d139030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137805 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
    | true =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
  have h2 (q : Pattern) (ha : d137806 q = 1) (hb : d139016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137807 q = 1) (hb : d139017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137808 q = 1) (hb : d139018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137809 q = 1) (hb : d139019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137815 q = 1) (hb : d139025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24536 q ha hb
    | true =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24537 q ha hb
  have h7 (q : Pattern) (ha : d137816 q = 1) (hb : d139026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137816, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137816, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137817 q = 1) (hb : d139027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137817, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137817, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137818 q = 1) (hb : d139028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137818, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137818, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137819 q = 1) (hb : d139029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137819, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137819, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137820 q = 1) (hb : d139030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137820, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137820, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24539 (p : Pattern) (ha : d137825 p = 1) (hb : d139035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137798 q = 1) (hb : d139008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137824 q = 1) (hb : d139034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137824, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137824, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137825 q = 1) (hb : d139035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137825, d139035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137825, d139035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24540 (p : Pattern) (ha : d137827 p = 1) (hb : d139037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d139012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137826 q = 1) (hb : d139036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137826, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137826, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137827 q = 1) (hb : d139037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137827, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137827, d139037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24541 (p : Pattern) (ha : d137834 p = 1) (hb : d139044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137832 q = 1) (hb : d139042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137832, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137832, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137833 q = 1) (hb : d139043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137833, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137833, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137834 q = 1) (hb : d139044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137834, d139044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137834, d139044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24542 (p : Pattern) (ha : d137837 p = 1) (hb : d139047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137835 q = 1) (hb : d139045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137835, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137835, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137836 q = 1) (hb : d139046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137836, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137836, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137837 q = 1) (hb : d139047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137837, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137837, d139047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24543 (p : Pattern) (ha : d137845 p = 1) (hb : d139056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53336 q = 1) (hb : d139051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d139051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12875 q hb ha
  have h3 (q : Pattern) (ha : d137841 q = 1) (hb : d139052 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137841, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137841, d139052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137842 q = 1) (hb : d139053 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137842, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137842, d139053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53348 q = 1) (hb : d138991 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q hb ha
  have h7 (q : Pattern) (ha : d137783 q = 1) (hb : d138992 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137784 q = 1) (hb : d138993 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137843 q = 1) (hb : d139054 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137843, d139054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137843, d139054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53350 q = 1) (hb : d138994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q hb ha
  have h12 (q : Pattern) (ha : d137785 q = 1) (hb : d138995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137786 q = 1) (hb : d138996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137787 q = 1) (hb : d138997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137844 q = 1) (hb : d139055 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137844, d139055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137844, d139055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137845 q = 1) (hb : d139056 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137845, d139056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137845, d139056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24544 (p : Pattern) (ha : d137851 p = 1) (hb : d139062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137846 q = 1) (hb : d139057 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137846, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24543 q ha hb
    | true =>
      simp only [d137846, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137847 q = 1) (hb : d139058 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137847, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137847, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137848 q = 1) (hb : d139059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137848, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137848, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137849 q = 1) (hb : d139060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137849, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137849, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137850 q = 1) (hb : d139061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137850, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137850, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137851 q = 1) (hb : d139062 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137851, d139062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137851, d139062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24545 (p : Pattern) (ha : d5727 p = 1) (hb : d74451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5721 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5722 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5723 q = 1) (hb : d74449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5723, d74449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5724 q = 1) (hb : d74450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5724, d74450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5725 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5725, d74451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5727 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24546 (p : Pattern) (ha : d137858 p = 1) (hb : d139070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53348 q = 1) (hb : d138991 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d138991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q hb ha
  have h3 (q : Pattern) (ha : d137783 q = 1) (hb : d138992 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137783, d138992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137784 q = 1) (hb : d138993 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137784, d138993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53350 q = 1) (hb : d138994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d138994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q hb ha
  have h7 (q : Pattern) (ha : d137785 q = 1) (hb : d138995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137785, d138995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137786 q = 1) (hb : d138996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137786, d138996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137787 q = 1) (hb : d138997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137787, d138997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74451 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74451 q = 1) (hb : d139065 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d139065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24545 q hb ha
  have h12 (q : Pattern) (ha : d137854 q = 1) (hb : d139066 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137854, d139066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137854, d139066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137855 q = 1) (hb : d139067 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137855, d139067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137855, d139067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137856 q = 1) (hb : d139068 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137856, d139068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137856, d139068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137857 q = 1) (hb : d139069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137857, d139069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137857, d139069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137858 q = 1) (hb : d139070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137858, d139070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137858, d139070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24547 (p : Pattern) (ha : d137864 p = 1) (hb : d139076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137859 q = 1) (hb : d139071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137859, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24546 q ha hb
    | true =>
      simp only [d137859, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137860 q = 1) (hb : d139072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137860, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137860, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137861 q = 1) (hb : d139073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137861, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137861, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137862 q = 1) (hb : d139074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137862, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137862, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137863 q = 1) (hb : d139075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137863, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137863, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137864 q = 1) (hb : d139076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137864, d139076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137864, d139076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24548 (p : Pattern) (ha : d137870 p = 1) (hb : d139082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137828 q = 1) (hb : d139038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137828, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24539 q ha hb
    | true =>
      simp only [d137828, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24540 q ha hb
  have h2 (q : Pattern) (ha : d137829 q = 1) (hb : d139039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137829, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137829, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137830 q = 1) (hb : d139040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137830, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137830, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137831 q = 1) (hb : d139041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137831, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137831, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137838 q = 1) (hb : d139048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137838, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24541 q ha hb
    | true =>
      simp only [d137838, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24542 q ha hb
  have h6 (q : Pattern) (ha : d137839 q = 1) (hb : d139049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137839, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137839, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137840 q = 1) (hb : d139050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137840, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137840, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137852 q = 1) (hb : d139063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137852, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24544 q ha hb
    | true =>
      simp only [d137852, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137805 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137853 q = 1) (hb : d139064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137853, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137853, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137865 q = 1) (hb : d139077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137865, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24547 q ha hb
    | true =>
      simp only [d137865, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137866 q = 1) (hb : d139078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137866, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137866, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137867 q = 1) (hb : d139079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137867, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137867, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137868 q = 1) (hb : d139080 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137868, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137868, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137869 q = 1) (hb : d139081 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137869, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137869, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137870 q = 1) (hb : d139082 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137870, d139082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137870, d139082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro24549 (p : Pattern) (ha : d137871 p = 1) (hb : d139083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137798 q = 1) (hb : d139008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137798, d139008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137824 q = 1) (hb : d139034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137824, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137824, d139034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137871 q = 1) (hb : d139083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137871, d139083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137871, d139083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24550 (p : Pattern) (ha : d137872 p = 1) (hb : d139084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137802 q = 1) (hb : d139012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137802, d139012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137826 q = 1) (hb : d139036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137826, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137826, d139036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137872 q = 1) (hb : d139084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137872, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137872, d139084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24551 (p : Pattern) (ha : d137877 p = 1) (hb : d139089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137797 q = 1) (hb : d139007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137797, d139007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137832 q = 1) (hb : d139042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137832, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137832, d139042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137833 q = 1) (hb : d139043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137833, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137833, d139043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137877 q = 1) (hb : d139089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137877, d139089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137877, d139089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24552 (p : Pattern) (ha : d137878 p = 1) (hb : d139090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137795 q = 1) (hb : d139005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24532 q ha hb
    | true =>
      simp only [d137795, d139005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137796 q = 1) (hb : d139006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137796, d139006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137801 q = 1) (hb : d139011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137801, d139011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137835 q = 1) (hb : d139045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137835, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137835, d139045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137836 q = 1) (hb : d139046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137836, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137836, d139046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137878 q = 1) (hb : d139090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137878, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137878, d139090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24553 (p : Pattern) (ha : d137882 p = 1) (hb : d139094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137846 q = 1) (hb : d139057 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137846, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24543 q ha hb
    | true =>
      simp only [d137846, d139057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137847 q = 1) (hb : d139058 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137847, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137847, d139058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137791 q = 1) (hb : d139001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24531 q ha hb
    | true =>
      simp only [d137791, d139001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137792 q = 1) (hb : d139002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137792, d139002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137848 q = 1) (hb : d139059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137848, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137848, d139059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137849 q = 1) (hb : d139060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137849, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137849, d139060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137850 q = 1) (hb : d139061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137850, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137850, d139061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137882 q = 1) (hb : d139094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137882, d139094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137882, d139094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24554 (p : Pattern) (ha : d137885 p = 1) (hb : d139097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137859 q = 1) (hb : d139071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137859, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24546 q ha hb
    | true =>
      simp only [d137859, d139071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137860 q = 1) (hb : d139072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137860, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137860, d139072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137861 q = 1) (hb : d139073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137861, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137861, d139073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137862 q = 1) (hb : d139074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137862, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137862, d139074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137863 q = 1) (hb : d139075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137863, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137863, d139075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137885 q = 1) (hb : d139097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137885, d139097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137885, d139097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24555 (p : Pattern) (ha : d137891 p = 1) (hb : d139103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137828 q = 1) (hb : d139038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137828, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24539 q ha hb
    | true =>
      simp only [d137828, d139038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24540 q ha hb
  have h2 (q : Pattern) (ha : d137829 q = 1) (hb : d139039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137829, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137829, d139039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137830 q = 1) (hb : d139040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137830, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137830, d139040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137831 q = 1) (hb : d139041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137831, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137831, d139041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137838 q = 1) (hb : d139048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137838, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24541 q ha hb
    | true =>
      simp only [d137838, d139048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24542 q ha hb
  have h6 (q : Pattern) (ha : d137839 q = 1) (hb : d139049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137839, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137839, d139049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137840 q = 1) (hb : d139050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137840, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137840, d139050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137852 q = 1) (hb : d139063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137852, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24544 q ha hb
    | true =>
      simp only [d137852, d139063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137805 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d137853 q = 1) (hb : d139064 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137853, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137853, d139064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137865 q = 1) (hb : d139077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137865, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24547 q ha hb
    | true =>
      simp only [d137865, d139077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137866 q = 1) (hb : d139078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137866, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137866, d139078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d137867 q = 1) (hb : d139079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137867, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137867, d139079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137868 q = 1) (hb : d139080 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137868, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137868, d139080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137869 q = 1) (hb : d139081 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137869, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137869, d139081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137873 q = 1) (hb : d139085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137873, d139085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24549 q ha hb
    | true =>
      simp only [d137873, d139085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24550 q ha hb
  have h17 (q : Pattern) (ha : d137874 q = 1) (hb : d139086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137874, d139086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137874, d139086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137875 q = 1) (hb : d139087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137875, d139087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137875, d139087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137876 q = 1) (hb : d139088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137876, d139088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137876, d139088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137879 q = 1) (hb : d139091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137879, d139091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24551 q ha hb
    | true =>
      simp only [d137879, d139091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24552 q ha hb
  have h21 (q : Pattern) (ha : d137880 q = 1) (hb : d139092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137880, d139092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137880, d139092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137881 q = 1) (hb : d139093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137881, d139093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137881, d139093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137883 q = 1) (hb : d139095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137883, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24553 q ha hb
    | true =>
      simp only [d137883, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24536 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d137815 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d137884 q = 1) (hb : d139096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137884, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d137884, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137886 q = 1) (hb : d139098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137886, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24554 q ha hb
    | true =>
      simp only [d137886, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137887 q = 1) (hb : d139099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137887, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137887, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d137888 q = 1) (hb : d139100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137888, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d137888, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d137889 q = 1) (hb : d139101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137889, d139101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d137889, d139101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d137890 q = 1) (hb : d139102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137890, d139102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137890, d139102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d137891 q = 1) (hb : d139103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137891, d139103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137891, d139103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro24556 (p : Pattern) (ha : d137898 p = 1) (hb : d139110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137805 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
    | true =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
  have h2 (q : Pattern) (ha : d137806 q = 1) (hb : d139016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137806, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137807 q = 1) (hb : d139017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137807, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137808 q = 1) (hb : d139018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137808, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137809 q = 1) (hb : d139019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137809, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137893 q = 1) (hb : d139105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137893, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
    | true =>
      simp only [d137893, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137894 q = 1) (hb : d139106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137894, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137894, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137895 q = 1) (hb : d139107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137895, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137895, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137896 q = 1) (hb : d139108 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137896, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137896, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137897 q = 1) (hb : d139109 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137897, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137897, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137898 q = 1) (hb : d139110 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137898, d139110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137898, d139110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24557 (p : Pattern) (ha : d137904 p = 1) (hb : d139116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137893 q = 1) (hb : d139105 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137893, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
    | true =>
      simp only [d137893, d139105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137894 q = 1) (hb : d139106 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137894, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137894, d139106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137895 q = 1) (hb : d139107 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137895, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137895, d139107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137896 q = 1) (hb : d139108 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137896, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137896, d139108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137897 q = 1) (hb : d139109 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137897, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137897, d139109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137899 q = 1) (hb : d139111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137899, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24537 q ha hb
    | true =>
      simp only [d137899, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137900 q = 1) (hb : d139112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137900, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137900, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137901 q = 1) (hb : d139113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137901, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137901, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137902 q = 1) (hb : d139114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137902, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137902, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137903 q = 1) (hb : d139115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137903, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137903, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137904 q = 1) (hb : d139116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137904, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137904, d139116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24558 (p : Pattern) (ha : d137911 p = 1) (hb : d139123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137883 q = 1) (hb : d139095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137883, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24553 q ha hb
    | true =>
      simp only [d137883, d139095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24536 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137815 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137884 q = 1) (hb : d139096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137884, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137884, d139096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137886 q = 1) (hb : d139098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137886, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24554 q ha hb
    | true =>
      simp only [d137886, d139098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137887 q = 1) (hb : d139099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137887, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137887, d139099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137888 q = 1) (hb : d139100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137888, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137888, d139100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137909 q = 1) (hb : d139121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137909, d139121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137909, d139121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137910 q = 1) (hb : d139122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137910, d139122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137910, d139122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137911 q = 1) (hb : d139123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137911, d139123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137911, d139123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24559 (p : Pattern) (ha : d137913 p = 1) (hb : d139125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137899 q = 1) (hb : d139111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137899, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24537 q ha hb
    | true =>
      simp only [d137899, d139111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137900 q = 1) (hb : d139112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137900, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137900, d139112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137901 q = 1) (hb : d139113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137901, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137901, d139113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137902 q = 1) (hb : d139114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137902, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137902, d139114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137903 q = 1) (hb : d139115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137903, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137903, d139115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137913 q = 1) (hb : d139125 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137913, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137913, d139125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24560 (p : Pattern) (ha : d137928 p = 1) (hb : d139143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53509 q = 1) (hb : d139131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d139131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12891 q hb ha
  have h3 (q : Pattern) (ha : d137919 q = 1) (hb : d139132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137919, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137919, d139132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137920 q = 1) (hb : d139133 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137920, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137920, d139133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53515 q = 1) (hb : d139134 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q hb ha
  have h7 (q : Pattern) (ha : d137921 q = 1) (hb : d139135 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137922 q = 1) (hb : d139136 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137923 q = 1) (hb : d139137 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137923, d139137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137923, d139137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d53520 q = 1) (hb : d139138 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q hb ha
  have h12 (q : Pattern) (ha : d137924 q = 1) (hb : d139139 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137925 q = 1) (hb : d139140 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137926 q = 1) (hb : d139141 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137927 q = 1) (hb : d139142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137927, d139142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137927, d139142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137928 q = 1) (hb : d139143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137928, d139143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137928, d139143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24561 (p : Pattern) (ha : d137933 p = 1) (hb : d139148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53515 q = 1) (hb : d139134 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q hb ha
  have h3 (q : Pattern) (ha : d137921 q = 1) (hb : d139135 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137922 q = 1) (hb : d139136 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53520 q = 1) (hb : d139138 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q hb ha
  have h7 (q : Pattern) (ha : d137924 q = 1) (hb : d139139 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137925 q = 1) (hb : d139140 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137926 q = 1) (hb : d139141 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137931 q = 1) (hb : d139146 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137931, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137931, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d137932 q = 1) (hb : d139147 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137932, d139147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137932, d139147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137933 q = 1) (hb : d139148 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137933, d139148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137933, d139148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro24562 (p : Pattern) (ha : d137939 p = 1) (hb : d139154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137929 q = 1) (hb : d139144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137929, d139144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24560 q ha hb
    | true =>
      simp only [d137929, d139144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137930 q = 1) (hb : d139145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137930, d139145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137930, d139145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137934 q = 1) (hb : d139149 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137934, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24561 q ha hb
    | true =>
      simp only [d137934, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137935 q = 1) (hb : d139150 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137935, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137935, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137936 q = 1) (hb : d139151 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137936, d139151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137936, d139151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137937 q = 1) (hb : d139152 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137937, d139152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137937, d139152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137938 q = 1) (hb : d139153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137938, d139153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137938, d139153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137939 q = 1) (hb : d139154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137939, d139154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137939, d139154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24563 (p : Pattern) (ha : d137941 p = 1) (hb : d139156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53520 q = 1) (hb : d139138 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q hb ha
  have h3 (q : Pattern) (ha : d137924 q = 1) (hb : d139139 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137925 q = 1) (hb : d139140 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137931 q = 1) (hb : d139146 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137931, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137931, d139146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137940 q = 1) (hb : d139155 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137940, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137940, d139155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137941 q = 1) (hb : d139156 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137941, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137941, d139156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro24564 (p : Pattern) (ha : d137947 p = 1) (hb : d139162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137934 q = 1) (hb : d139149 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137934, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24561 q ha hb
    | true =>
      simp only [d137934, d139149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137935 q = 1) (hb : d139150 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137935, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137935, d139150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137942 q = 1) (hb : d139157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137942, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24563 q ha hb
    | true =>
      simp only [d137942, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137943 q = 1) (hb : d139158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137943, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137943, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137944 q = 1) (hb : d139159 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137944, d139159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137944, d139159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137945 q = 1) (hb : d139160 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137945, d139160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137945, d139160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137946 q = 1) (hb : d139161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137946, d139161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137946, d139161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137947 q = 1) (hb : d139162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137947, d139162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137947, d139162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro24565 (p : Pattern) (ha : d5771 p = 1) (hb : d74495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5765 q = 1) (hb : d74491 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5765, d74491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
  have h2 (q : Pattern) (ha : d5721 q = 1) (hb : d74447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9307 q ha hb
    | true =>
      simp only [d5721, d74447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5766 q = 1) (hb : d74492 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5766, d74492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5722 q = 1) (hb : d74448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5722, d74448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5767 q = 1) (hb : d74493 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5767, d74493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5768 q = 1) (hb : d74494 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5768, d74494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5769 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5769, d74495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d5771 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24566 (p : Pattern) (ha : d137959 p = 1) (hb : d139170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53515 q = 1) (hb : d139134 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d139134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q hb ha
  have h3 (q : Pattern) (ha : d137921 q = 1) (hb : d139135 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137921, d139135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137922 q = 1) (hb : d139136 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137922, d139136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53520 q = 1) (hb : d139138 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d139138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q hb ha
  have h7 (q : Pattern) (ha : d137924 q = 1) (hb : d139139 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137924, d139139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137925 q = 1) (hb : d139140 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137925, d139140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137926 q = 1) (hb : d139141 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137926, d139141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74495 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d74495 q = 1) (hb : d139165 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d139165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d139165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24565 q hb ha
  have h12 (q : Pattern) (ha : d137955 q = 1) (hb : d139166 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137955, d139166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137955, d139166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137956 q = 1) (hb : d139167 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137956, d139167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137956, d139167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137957 q = 1) (hb : d139168 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d137957, d139168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137957, d139168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137958 q = 1) (hb : d139169 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d137958, d139169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137958, d139169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137959 q = 1) (hb : d139170 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d137959, d139170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137959, d139170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro24567 (p : Pattern) (ha : d137965 p = 1) (hb : d139176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137960 q = 1) (hb : d139171 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137960, d139171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24566 q ha hb
    | true =>
      simp only [d137960, d139171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137961 q = 1) (hb : d139172 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137961, d139172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137961, d139172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137962 q = 1) (hb : d139173 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137962, d139173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137962, d139173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137963 q = 1) (hb : d139174 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137963, d139174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137963, d139174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137964 q = 1) (hb : d139175 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137964, d139175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137964, d139175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137965 q = 1) (hb : d139176 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137965, d139176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137965, d139176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24568 (p : Pattern) (ha : d137971 p = 1) (hb : d139182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137948 q = 1) (hb : d139163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137948, d139163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24562 q ha hb
    | true =>
      simp only [d137948, d139163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24564 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137954 q = 1) (hb : d139164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137954, d139164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137954, d139164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137966 q = 1) (hb : d139177 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137966, d139177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24567 q ha hb
    | true =>
      simp only [d137966, d139177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137967 q = 1) (hb : d139178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137967, d139178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137967, d139178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137968 q = 1) (hb : d139179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137968, d139179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137968, d139179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137969 q = 1) (hb : d139180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137969, d139180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137969, d139180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137970 q = 1) (hb : d139181 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137970, d139181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137970, d139181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137971 q = 1) (hb : d139182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137971, d139182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137971, d139182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro24569 (p : Pattern) (ha : d137952 p = 1) (hb : d139187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137942 q = 1) (hb : d139157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137942, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24563 q ha hb
    | true =>
      simp only [d137942, d139157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137943 q = 1) (hb : d139158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137943, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137943, d139158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137949 q = 1) (hb : d139184 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137949, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137949, d139184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137950 q = 1) (hb : d139185 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137950, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137950, d139185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137951 q = 1) (hb : d139186 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137951, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137951, d139186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137952 q = 1) (hb : d139187 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137952, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137952, d139187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24570 (p : Pattern) (ha : d137978 p = 1) (hb : d139193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137973 q = 1) (hb : d139188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137973, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24569 q ha hb
    | true =>
      simp only [d137973, d139188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137974 q = 1) (hb : d139189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137974, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137974, d139189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137975 q = 1) (hb : d139190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137975, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137975, d139190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137976 q = 1) (hb : d139191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137976, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137976, d139191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137977 q = 1) (hb : d139192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137977, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137977, d139192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137978 q = 1) (hb : d139193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137978, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137978, d139193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24571 (p : Pattern) (ha : d137984 p = 1) (hb : d139199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137811 q = 1) (hb : d139021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137811, d139021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137811, d139021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24535 q ha hb
  have h2 (q : Pattern) (ha : d137812 q = 1) (hb : d139022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137812, d139022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137812, d139022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137821 q = 1) (hb : d139031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137821, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24535 q ha hb
    | true =>
      simp only [d137821, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24538 q ha hb
  have h4 (q : Pattern) (ha : d137822 q = 1) (hb : d139032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137822, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137822, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137823 q = 1) (hb : d139033 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137823, d139033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137823, d139033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137892 q = 1) (hb : d139104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137892, d139104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24548 q ha hb
    | true =>
      simp only [d137892, d139104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24555 q ha hb
  have h7 (q : Pattern) (ha : d137905 q = 1) (hb : d139117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137905, d139117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24556 q ha hb
    | true =>
      simp only [d137905, d139117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24557 q ha hb
  have h8 (q : Pattern) (ha : d137906 q = 1) (hb : d139118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137906, d139118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137906, d139118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137907 q = 1) (hb : d139119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137907, d139119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137907, d139119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d137908 q = 1) (hb : d139120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137908, d139120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137908, d139120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137912 q = 1) (hb : d139124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137912, d139124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137912, d139124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24558 q ha hb
  have h12 (q : Pattern) (ha : d137914 q = 1) (hb : d139126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137914, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137914, d139126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24559 q ha hb
  have h13 (q : Pattern) (ha : d137915 q = 1) (hb : d139127 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137915, d139127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137915, d139127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137916 q = 1) (hb : d139128 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137916, d139128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137916, d139128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d137917 q = 1) (hb : d139129 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137917, d139129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137917, d139129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d137918 q = 1) (hb : d139130 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137918, d139130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137918, d139130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137972 q = 1) (hb : d139183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137972, d139183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137972, d139183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24568 q ha hb
  have h18 (q : Pattern) (ha : d137979 q = 1) (hb : d139194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137979, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137979, d139194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24570 q ha hb
  have h19 (q : Pattern) (ha : d137980 q = 1) (hb : d139195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137980, d139195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137980, d139195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137981 q = 1) (hb : d139196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137981, d139196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137981, d139196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137982 q = 1) (hb : d139197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137982, d139197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d137982, d139197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d137983 q = 1) (hb : d139198 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137983, d139198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137983, d139198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d137984 q = 1) (hb : d139199 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137984, d139199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137984, d139199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro24572 (p : Pattern) (ha : d137990 p = 1) (hb : d139205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137985 q = 1) (hb : d139200 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137985, d139200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137985, d139200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24571 q ha hb
  have h2 (q : Pattern) (ha : d137986 q = 1) (hb : d139201 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137986, d139201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137986, d139201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137987 q = 1) (hb : d139202 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137987, d139202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137987, d139202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137988 q = 1) (hb : d139203 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137988, d139203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137988, d139203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137989 q = 1) (hb : d139204 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137989, d139204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137989, d139204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137990 q = 1) (hb : d139205 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137990, d139205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137990, d139205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24573 (p : Pattern) (ha : d137996 p = 1) (hb : d139211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d137149 q = 1) (hb : d138336 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137149, d138336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24381 q ha hb
    | true =>
      simp only [d137149, d138336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24404 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137358 q = 1) (hb : d138552 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137358, d138552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137358, d138552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24446 q ha hb
  have h3 (q : Pattern) (ha : d137359 q = 1) (hb : d138553 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137359, d138553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d137359, d138553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137568 q = 1) (hb : d138769 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137568, d138769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137568, d138769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24488 q ha hb
  have h5 (q : Pattern) (ha : d137569 q = 1) (hb : d138770 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137569, d138770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137569, d138770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137570 q = 1) (hb : d138771 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137570, d138771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137570, d138771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137779 q = 1) (hb : d138987 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137779, d138987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137779, d138987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24530 q ha hb
  have h8 (q : Pattern) (ha : d137780 q = 1) (hb : d138988 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137780, d138988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137780, d138988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137781 q = 1) (hb : d138989 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137781, d138989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137781, d138989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137782 q = 1) (hb : d138990 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d137782, d138990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137782, d138990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137991 q = 1) (hb : d139206 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137991, d139206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137991, d139206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24572 q ha hb
  have h12 (q : Pattern) (ha : d137992 q = 1) (hb : d139207 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137992, d139207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137992, d139207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137993 q = 1) (hb : d139208 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137993, d139208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137993, d139208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137994 q = 1) (hb : d139209 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d137994, d139209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137994, d139209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137995 q = 1) (hb : d139210 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d137995, d139210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137995, d139210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137996 q = 1) (hb : d139211 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d137996, d139211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137996, d139211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro24574 (p : Pattern) (ha : d138002 p = 1) (hb : d139217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137997 q = 1) (hb : d139212 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d137997, d139212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24573 q ha hb
    | true =>
      simp only [d137997, d139212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137998 q = 1) (hb : d139213 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d137998, d139213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137998, d139213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137999 q = 1) (hb : d139214 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d137999, d139214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137999, d139214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138000 q = 1) (hb : d139215 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d138000, d139215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138000, d139215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138001 q = 1) (hb : d139216 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d138001, d139216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138001, d139216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138002 q = 1) (hb : d139217 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d138002, d139217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138002, d139217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24575 (p : Pattern) (ha : d138008 p = 1) (hb : d139223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138003 q = 1) (hb : d139218 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d138003, d139218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24574 q ha hb
    | true =>
      simp only [d138003, d139218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138004 q = 1) (hb : d139219 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d138004, d139219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138004, d139219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138005 q = 1) (hb : d139220 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d138005, d139220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138005, d139220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138006 q = 1) (hb : d139221 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d138006, d139221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138006, d139221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138007 q = 1) (hb : d139222 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d138007, d139222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138007, d139222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138008 q = 1) (hb : d139223 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d138008, d139223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138008, d139223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24576 (p : Pattern) (ha : d138014 p = 1) (hb : d139229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138009 q = 1) (hb : d139224 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d138009, d139224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24575 q ha hb
    | true =>
      simp only [d138009, d139224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138010 q = 1) (hb : d139225 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d138010, d139225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138010, d139225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138011 q = 1) (hb : d139226 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d138011, d139226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138011, d139226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138012 q = 1) (hb : d139227 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d138012, d139227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138012, d139227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138013 q = 1) (hb : d139228 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d138013, d139228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138013, d139228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138014 q = 1) (hb : d139229 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d138014, d139229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138014, d139229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24577 (p : Pattern) (ha : d138020 p = 1) (hb : d139235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138015 q = 1) (hb : d139230 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d138015, d139230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24576 q ha hb
    | true =>
      simp only [d138015, d139230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138016 q = 1) (hb : d139231 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d138016, d139231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138016, d139231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138017 q = 1) (hb : d139232 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d138017, d139232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138017, d139232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138018 q = 1) (hb : d139233 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d138018, d139233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138018, d139233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138019 q = 1) (hb : d139234 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d138019, d139234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138019, d139234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138020 q = 1) (hb : d139235 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d138020, d139235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138020, d139235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24578 (p : Pattern) (ha : d138026 p = 1) (hb : d139241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138021 q = 1) (hb : d139236 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d138021, d139236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24577 q ha hb
    | true =>
      simp only [d138021, d139236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138022 q = 1) (hb : d139237 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d138022, d139237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138022, d139237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138023 q = 1) (hb : d139238 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d138023, d139238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138023, d139238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138024 q = 1) (hb : d139239 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d138024, d139239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138024, d139239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138025 q = 1) (hb : d139240 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d138025, d139240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138025, d139240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138026 q = 1) (hb : d139241 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d138026, d139241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138026, d139241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24579 (p : Pattern) (ha : d138032 p = 1) (hb : d139247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138027 q = 1) (hb : d139242 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d138027, d139242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24578 q ha hb
    | true =>
      simp only [d138027, d139242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138028 q = 1) (hb : d139243 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d138028, d139243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138028, d139243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138029 q = 1) (hb : d139244 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d138029, d139244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138029, d139244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138030 q = 1) (hb : d139245 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d138030, d139245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138030, d139245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138031 q = 1) (hb : d139246 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d138031, d139246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138031, d139246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138032 q = 1) (hb : d139247 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d138032, d139247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138032, d139247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24580 (p : Pattern) (ha : d138038 p = 1) (hb : d139253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138033 q = 1) (hb : d139248 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d138033, d139248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24579 q ha hb
    | true =>
      simp only [d138033, d139248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138034 q = 1) (hb : d139249 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d138034, d139249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138034, d139249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138035 q = 1) (hb : d139250 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d138035, d139250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138035, d139250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138036 q = 1) (hb : d139251 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d138036, d139251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138036, d139251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138037 q = 1) (hb : d139252 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d138037, d139252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138037, d139252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138038 q = 1) (hb : d139253 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d138038, d139253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138038, d139253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24581 (p : Pattern) (ha : d53647 p = 1) (hb : d135431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24108 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24109 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24128 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24129 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
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
theorem andIntro24582 (p : Pattern) (ha : d53655 p = 1) (hb : d135431 p = 1) : d138288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d135431 q = 1) : d138058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24112 q ha hb
    | true =>
      simp only [d204, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24101 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d135431 q = 1) : d138110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d135431 q = 1) : d138111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d135431 q = 1) : d138112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d135431 q = 1) : d138113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d135431 q = 1) : d138288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24583 (p : Pattern) (ha : d53665 p = 1) (hb : d135431 p = 1) : d138323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d135431 q = 1) : d138086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24115 q ha hb
    | true =>
      simp only [d244, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24105 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d135431 q = 1) : d138319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d135431 q = 1) : d138320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d135431 q = 1) : d138321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d135431 q = 1) : d138322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d135431 q = 1) : d138323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24584 (p : Pattern) (ha : d53671 p = 1) (hb : d135431 p = 1) : d139264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d135431 q = 1) : d138115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24125 q ha hb
    | true =>
      simp only [d292, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24126 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d135431 q = 1) : d138116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d135431 q = 1) : d139254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d135431 q = 1) : d139255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d135431 q = 1) : d138289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24582 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d135431 q = 1) : d139256 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d135431 q = 1) : d139257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d135431 q = 1) : d139258 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d135431 q = 1) : d139259 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d135431 q = 1) : d138324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24583 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d135431 q = 1) : d139260 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d135431 q = 1) : d139261 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d135431 q = 1) : d139262 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d135431 q = 1) : d139263 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d135431 q = 1) : d139264 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24585 (p : Pattern) (ha : d53677 p = 1) (hb : d135431 p = 1) : d139270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24581 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d135431 q = 1) : d139265 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24584 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d135431 q = 1) : d139266 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d135431 q = 1) : d139267 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d135431 q = 1) : d139268 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d135431 q = 1) : d139269 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d135431 q = 1) : d139270 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro24586 (p : Pattern) (ha : d53680 p = 1) (hb : d135431 p = 1) : d139273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d135431 q = 1) : d138158 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24153 q ha hb
    | true =>
      simp only [d502, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24154 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d135431 q = 1) : d138215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d135431 q = 1) : d138216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d135431 q = 1) : d138217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d135431 q = 1) : d138218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d135431 q = 1) : d139273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24587 (p : Pattern) (ha : d53691 p = 1) (hb : d135431 p = 1) : d139283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d135431 q = 1) : d138190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24181 q ha hb
    | true =>
      simp only [d53686, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24160 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d135431 q = 1) : d139279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d135431 q = 1) : d139280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d135431 q = 1) : d139281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d135431 q = 1) : d139282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d135431 q = 1) : d139283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24588 (p : Pattern) (ha : d53697 p = 1) (hb : d135431 p = 1) : d139289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d135431 q = 1) : d138220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24152 q ha hb
    | true =>
      simp only [d508, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24155 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d135431 q = 1) : d138221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d135431 q = 1) : d139271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d135431 q = 1) : d139272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d135431 q = 1) : d139274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24586 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d135431 q = 1) : d139275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d135431 q = 1) : d139276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d135431 q = 1) : d139277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d135431 q = 1) : d139278 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d135431 q = 1) : d139284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24587 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d135431 q = 1) : d139285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d135431 q = 1) : d139286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d135431 q = 1) : d139287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d135431 q = 1) : d139288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d135431 q = 1) : d139289 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24589 (p : Pattern) (ha : d53703 p = 1) (hb : d135431 p = 1) : d139295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d135431 q = 1) : d139290 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24588 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d135431 q = 1) : d139291 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d135431 q = 1) : d139292 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d135431 q = 1) : d139293 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d135431 q = 1) : d139294 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d135431 q = 1) : d139295 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24590 (p : Pattern) (ha : d53707 p = 1) (hb : d135431 p = 1) : d139299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d135431 q = 1) : d138371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24191 q ha hb
    | true =>
      simp only [d794, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24192 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d135431 q = 1) : d138372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d135431 q = 1) : d138373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d135431 q = 1) : d138374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d135431 q = 1) : d138375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d135431 q = 1) : d139299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24591 (p : Pattern) (ha : d53718 p = 1) (hb : d135431 p = 1) : d139310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d135431 q = 1) : d139305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24220 q ha hb
    | true =>
      simp only [d53713, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24198 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d135431 q = 1) : d139306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d135431 q = 1) : d139307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d135431 q = 1) : d139308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d135431 q = 1) : d139309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d135431 q = 1) : d139310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24592 (p : Pattern) (ha : d53724 p = 1) (hb : d135431 p = 1) : d139316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d135431 q = 1) : d138377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24190 q ha hb
    | true =>
      simp only [d800, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24193 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d135431 q = 1) : d138378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d135431 q = 1) : d139297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d135431 q = 1) : d139298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d135431 q = 1) : d139300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24590 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d135431 q = 1) : d139301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d135431 q = 1) : d139302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d135431 q = 1) : d139303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d135431 q = 1) : d139304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d135431 q = 1) : d139311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24591 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d135431 q = 1) : d139312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d135431 q = 1) : d139313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d135431 q = 1) : d139314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d135431 q = 1) : d139315 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d135431 q = 1) : d139316 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24593 (p : Pattern) (ha : d53730 p = 1) (hb : d135431 p = 1) : d139322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d135431 q = 1) : d139317 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24592 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d135431 q = 1) : d139318 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d135431 q = 1) : d139319 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d135431 q = 1) : d139320 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d135431 q = 1) : d139321 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d135431 q = 1) : d139322 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24594 (p : Pattern) (ha : d53735 p = 1) (hb : d135431 p = 1) : d139327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d135431 q = 1) : d138588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24231 q ha hb
    | true =>
      simp only [d1173, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24232 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d135431 q = 1) : d138589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d135431 q = 1) : d138590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d135431 q = 1) : d138591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d135431 q = 1) : d138592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d135431 q = 1) : d139327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d139327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d139327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24595 (p : Pattern) (ha : d53746 p = 1) (hb : d135431 p = 1) : d139338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d135431 q = 1) : d139333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d139333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24260 q ha hb
    | true =>
      simp only [d53741, d139333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24238 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d135431 q = 1) : d139334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d139334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d139334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d135431 q = 1) : d139335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d139335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d139335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d135431 q = 1) : d139336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d139336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d139336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d135431 q = 1) : d139337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d139337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d139337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d135431 q = 1) : d139338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d139338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d139338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24596 (p : Pattern) (ha : d53752 p = 1) (hb : d135431 p = 1) : d139344 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d135431 q = 1) : d138594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24230 q ha hb
    | true =>
      simp only [d1179, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24233 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d135431 q = 1) : d138595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d135431 q = 1) : d139325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d139325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d139325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d135431 q = 1) : d139326 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d139326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d139326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d135431 q = 1) : d139328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d139328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d139328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24594 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d135431 q = 1) : d139329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d139329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d139329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d135431 q = 1) : d139330 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d139330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d139330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d135431 q = 1) : d139331 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d139331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d139331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d135431 q = 1) : d139332 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d139332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d139332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d135431 q = 1) : d139339 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d139339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d139339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24595 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d135431 q = 1) : d139340 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d139340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d139340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d135431 q = 1) : d139341 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d139341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d139341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d135431 q = 1) : d139342 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d139342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d139342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d135431 q = 1) : d139343 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d139343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d139343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d135431 q = 1) : d139344 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d139344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d139344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24597 (p : Pattern) (ha : d53758 p = 1) (hb : d135431 p = 1) : d139350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d135431 q = 1) : d139345 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d139345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d139345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24596 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d135431 q = 1) : d139346 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d139346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d139346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d135431 q = 1) : d139347 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d139347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d139347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d135431 q = 1) : d139348 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d139348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d139348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d135431 q = 1) : d139349 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d139349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d139349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d135431 q = 1) : d139350 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d139350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d139350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24598 (p : Pattern) (ha : d53764 p = 1) (hb : d135431 p = 1) : d139356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d135431 q = 1) : d138806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24271 q ha hb
    | true =>
      simp only [d1634, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24272 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d135431 q = 1) : d138807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d135431 q = 1) : d138808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d135431 q = 1) : d138809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d135431 q = 1) : d138810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d135431 q = 1) : d139356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d139356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d139356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24599 (p : Pattern) (ha : d53775 p = 1) (hb : d135431 p = 1) : d139367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d135431 q = 1) : d139362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d139362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24300 q ha hb
    | true =>
      simp only [d53770, d139362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24278 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d135431 q = 1) : d139363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d139363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d139363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d135431 q = 1) : d139364 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d139364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d139364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d135431 q = 1) : d139365 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d139365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d139365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d135431 q = 1) : d139366 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d139366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d139366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d135431 q = 1) : d139367 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d139367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d139367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24600 (p : Pattern) (ha : d53781 p = 1) (hb : d135431 p = 1) : d139373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d135431 q = 1) : d138812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24270 q ha hb
    | true =>
      simp only [d1640, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24273 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d135431 q = 1) : d138813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d135431 q = 1) : d139354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d139354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d139354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d135431 q = 1) : d139355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d139355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d139355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d135431 q = 1) : d139357 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d139357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d139357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24598 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d135431 q = 1) : d139358 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d139358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d139358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d135431 q = 1) : d139359 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d139359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d139359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d135431 q = 1) : d139360 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d139360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d139360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d135431 q = 1) : d139361 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d139361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d139361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d135431 q = 1) : d139368 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d139368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d139368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24599 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d135431 q = 1) : d139369 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d139369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d139369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d135431 q = 1) : d139370 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d139370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d139370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d135431 q = 1) : d139371 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d139371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d139371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d135431 q = 1) : d139372 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d139372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d139372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d135431 q = 1) : d139373 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d139373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d139373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24601 (p : Pattern) (ha : d53787 p = 1) (hb : d135431 p = 1) : d139379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d135431 q = 1) : d139374 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d139374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d139374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24600 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d135431 q = 1) : d139375 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d139375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d139375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d135431 q = 1) : d139376 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d139376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d139376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d135431 q = 1) : d139377 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d139377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d139377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d135431 q = 1) : d139378 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d139378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d139378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d135431 q = 1) : d139379 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d139379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d139379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24602 (p : Pattern) (ha : d53794 p = 1) (hb : d135431 p = 1) : d139386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d135431 q = 1) : d139025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24311 q ha hb
    | true =>
      simp only [d2117, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24312 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d135431 q = 1) : d139026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d135431 q = 1) : d139027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d135431 q = 1) : d139028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d135431 q = 1) : d139029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d135431 q = 1) : d139386 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d139386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d139386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24603 (p : Pattern) (ha : d53805 p = 1) (hb : d135431 p = 1) : d139397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d135431 q = 1) : d139392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d139392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24340 q ha hb
    | true =>
      simp only [d53800, d139392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24318 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d135431 q = 1) : d139393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d139393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d139393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d135431 q = 1) : d139394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d139394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d139394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d135431 q = 1) : d139395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d139395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d139395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d135431 q = 1) : d139396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d139396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d139396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d135431 q = 1) : d139397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d139397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d139397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24604 (p : Pattern) (ha : d53811 p = 1) (hb : d135431 p = 1) : d139403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d135431 q = 1) : d139031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24310 q ha hb
    | true =>
      simp only [d2123, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24313 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d135431 q = 1) : d139032 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d135431 q = 1) : d139384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d139384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d139384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d135431 q = 1) : d139385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d139385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d139385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d135431 q = 1) : d139387 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d139387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d139387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24602 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d135431 q = 1) : d139388 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d139388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d139388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d135431 q = 1) : d139389 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d139389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d139389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d135431 q = 1) : d139390 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d139390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d139390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d135431 q = 1) : d139391 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d139391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d139391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d135431 q = 1) : d139398 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d139398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d139398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24603 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d135431 q = 1) : d139399 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d139399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d139399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d135431 q = 1) : d139400 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d139400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d139400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d135431 q = 1) : d139401 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d139401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d139401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d135431 q = 1) : d139402 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d139402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d139402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d135431 q = 1) : d139403 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d139403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d139403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro24605 (p : Pattern) (ha : d53817 p = 1) (hb : d135431 p = 1) : d139409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d135431 q = 1) : d139404 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d139404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d139404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24604 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d135431 q = 1) : d139405 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d139405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d139405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d135431 q = 1) : d139406 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d139406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d139406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d135431 q = 1) : d139407 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d139407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d139407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d135431 q = 1) : d139408 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d139408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d139408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d135431 q = 1) : d139409 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d139409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d139409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24606 (p : Pattern) (ha : d53823 p = 1) (hb : d135431 p = 1) : d139415 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d135431 q = 1) : d139296 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24585 q ha hb
    | true =>
      simp only [d53704, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24589 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d135431 q = 1) : d139323 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24593 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d135431 q = 1) : d139324 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d135431 q = 1) : d139351 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d139351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d139351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24597 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d135431 q = 1) : d139352 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d139352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d139352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d135431 q = 1) : d139353 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d139353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d139353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d135431 q = 1) : d139380 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d139380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d139380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24601 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d135431 q = 1) : d139381 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d139381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d139381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d135431 q = 1) : d139382 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d139382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d139382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d135431 q = 1) : d139383 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d139383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d139383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d135431 q = 1) : d139410 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d139410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d139410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24605 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d135431 q = 1) : d139411 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d139411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d139411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d135431 q = 1) : d139412 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d139412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d139412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d135431 q = 1) : d139413 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d139413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d139413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d135431 q = 1) : d139414 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d139414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d139414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d135431 q = 1) : d139415 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d139415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d139415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro24607 (p : Pattern) (ha : d53829 p = 1) (hb : d135431 p = 1) : d139421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d135431 q = 1) : d139416 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d139416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24606 q ha hb
    | true =>
      simp only [d53824, d139416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d135431 q = 1) : d139417 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d139417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d139417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d135431 q = 1) : d139418 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d139418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d139418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d135431 q = 1) : d139419 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d139419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d139419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d135431 q = 1) : d139420 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d139420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d139420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d135431 q = 1) : d139421 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d139421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d139421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24608 (p : Pattern) (ha : d53835 p = 1) (hb : d135431 p = 1) : d139427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d135431 q = 1) : d139422 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d139422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24607 q ha hb
    | true =>
      simp only [d53830, d139422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d135431 q = 1) : d139423 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d139423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d139423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d135431 q = 1) : d139424 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d139424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d139424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d135431 q = 1) : d139425 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d139425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d139425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d135431 q = 1) : d139426 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d139426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d139426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d135431 q = 1) : d139427 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d139427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d139427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24609 (p : Pattern) (ha : d53841 p = 1) (hb : d135431 p = 1) : d139433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d135431 q = 1) : d139428 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d139428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24608 q ha hb
    | true =>
      simp only [d53836, d139428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d135431 q = 1) : d139429 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d139429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d139429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d135431 q = 1) : d139430 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d139430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d139430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d135431 q = 1) : d139431 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d139431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d139431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d135431 q = 1) : d139432 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d139432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d139432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d135431 q = 1) : d139433 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d139433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d139433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24610 (p : Pattern) (ha : d53847 p = 1) (hb : d135432 p = 1) : d139439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d135431 q = 1) : d139434 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d139434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24609 q ha hb
    | true =>
      simp only [d53842, d139434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d135431 q = 1) : d139435 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d139435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d139435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53844 q = 1) (hb : d135432 q = 1) : d139436 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d135432, d139436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d135432, d139436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53845 q = 1) (hb : d135432 q = 1) : d139437 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d139437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53845, d139437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53846 q = 1) (hb : d135432 q = 1) : d139438 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d139438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53846, d139438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53847 q = 1) (hb : d135432 q = 1) : d139439 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d139439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53847, d139439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro24611 (p : Pattern) (ha : d53853 p = 1) (hb : d135432 p = 1) : d139445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d135432 q = 1) : d139440 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d139440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24610 q ha hb
    | true =>
      simp only [d53848, d139440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d135432 q = 1) : d139441 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d139441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d139441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d135432 q = 1) : d139442 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d139442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d139442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d135432 q = 1) : d139443 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d139443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d139443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d135432 q = 1) : d139444 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d139444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d139444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d135432 q = 1) : d139445 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d139445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d139445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24612 (p : Pattern) (ha : d53859 p = 1) (hb : d135432 p = 1) : d139451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d135432 q = 1) : d139446 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d139446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24611 q ha hb
    | true =>
      simp only [d53854, d139446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d135432 q = 1) : d139447 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d139447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d139447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d135432 q = 1) : d139448 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d139448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d139448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d135432 q = 1) : d139449 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d139449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d139449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d135432 q = 1) : d139450 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d139450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d139450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d135432 q = 1) : d139451 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d139451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d139451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24613 (p : Pattern) (ha : d53865 p = 1) (hb : d135432 p = 1) : d139457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135432 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d135432 q = 1) : d139452 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d139452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24612 q ha hb
    | true =>
      simp only [d53860, d139452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d135432 q = 1) : d139453 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d139453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d139453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d135432 q = 1) : d139454 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d139454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d139454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d135432 q = 1) : d139455 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d139455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d139455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d135432 q = 1) : d139456 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d139456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d139456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d135432 q = 1) : d139457 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d139457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d139457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24614 (p : Pattern) (ha : d136963 p = 1) (hb : d138107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d136959 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d136959, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136960 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136960, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d136961 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d136961, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136962 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d136962, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d136963 q = 1) (hb : d138107 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136963, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136963, d138107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24615 (p : Pattern) (ha : d136979 p = 1) (hb : d138114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136869 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
    | true =>
      simp only [d136869, d138051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d136959 q = 1) (hb : d138103 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d136959, d138103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136960 q = 1) (hb : d138104 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136960, d138104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d136961 q = 1) (hb : d138105 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d136961, d138105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136962 q = 1) (hb : d138106 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136962, d138106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d136968 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d136972 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d136975 q = 1) (hb : d138110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d136975, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d136976 q = 1) (hb : d138111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d136976, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d136977 q = 1) (hb : d138112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136977, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d136977, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d136978 q = 1) (hb : d138113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136978, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d136978, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d136979 q = 1) (hb : d138114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136979, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136979, d138114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24616 (p : Pattern) (ha : d136988 p = 1) (hb : d138288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136876 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
    | true =>
      simp only [d136876, d138058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d136975 q = 1) (hb : d138110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d136975, d138110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d136976 q = 1) (hb : d138111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136976, d138111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136986 q = 1) (hb : d138112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136986, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136986, d138112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d136987 q = 1) (hb : d138113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136987, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136987, d138113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136988 q = 1) (hb : d138288 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136988, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136988, d138288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24617 (p : Pattern) (ha : d137010 p = 1) (hb : d138323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136903 q = 1) (hb : d138086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
    | true =>
      simp only [d136903, d138086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137006 q = 1) (hb : d138319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137006, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137006, d138319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137007 q = 1) (hb : d138320 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137007, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137007, d138320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137008 q = 1) (hb : d138321 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137008, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137008, d138321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137009 q = 1) (hb : d138322 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137009, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137009, d138322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137010 q = 1) (hb : d138323 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137010, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137010, d138323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24618 (p : Pattern) (ha : d137016 p = 1) (hb : d139264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136980 q = 1) (hb : d138115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136980, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24614 q ha hb
    | true =>
      simp only [d136980, d138115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24615 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136982 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d136983 q = 1) (hb : d138116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136983, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136983, d138116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d136984 q = 1) (hb : d139254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136984, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136984, d139254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136985 q = 1) (hb : d139255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136985, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136985, d139255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d136989 q = 1) (hb : d138289 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136989, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d136989, d138289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24616 q ha hb
  have h8 (q : Pattern) (ha : d136990 q = 1) (hb : d139256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136990, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136990, d139256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d136991 q = 1) (hb : d139257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136991, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136991, d139257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d136992 q = 1) (hb : d139258 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136992, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136992, d139258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d136993 q = 1) (hb : d139259 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136993, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136993, d139259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d137011 q = 1) (hb : d138324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137011, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137011, d138324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24617 q ha hb
  have h13 (q : Pattern) (ha : d137012 q = 1) (hb : d139260 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137012, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137012, d139260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d137013 q = 1) (hb : d139261 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137013, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137013, d139261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d137014 q = 1) (hb : d139262 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137014, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d137014, d139262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d137015 q = 1) (hb : d139263 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137015, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137015, d139263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137016 q = 1) (hb : d139264 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137016, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137016, d139264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24619 (p : Pattern) (ha : d137022 p = 1) (hb : d139270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136919 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137017 q = 1) (hb : d139265 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137017, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137017, d139265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24618 q ha hb
  have h3 (q : Pattern) (ha : d137018 q = 1) (hb : d139266 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137018, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137018, d139266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137019 q = 1) (hb : d139267 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137019, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137019, d139267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137020 q = 1) (hb : d139268 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137020, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137020, d139268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137021 q = 1) (hb : d139269 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137021, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137021, d139269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137022 q = 1) (hb : d139270 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137022, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137022, d139270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24620 (p : Pattern) (ha : d137072 p = 1) (hb : d138212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d137061 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h5 (q : Pattern) (ha : d137062 q = 1) (hb : d138208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137062, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d137062, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137068 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137069 q = 1) (hb : d138209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137069, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137069, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137070 q = 1) (hb : d138210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137070, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137070, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137071 q = 1) (hb : d138211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137071, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137071, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137072 q = 1) (hb : d138212 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137072, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137072, d138212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24621 (p : Pattern) (ha : d137091 p = 1) (hb : d138219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137061 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d136958 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24369 q ha hb
    | true =>
      simp only [d136958, d138142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24355 q ha hb
  have h4 (q : Pattern) (ha : d137062 q = 1) (hb : d138208 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137062, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137062, d138208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137068 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137069 q = 1) (hb : d138209 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137069, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137069, d138209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137070 q = 1) (hb : d138210 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137070, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137070, d138210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137071 q = 1) (hb : d138211 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137071, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137071, d138211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137081 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d137083 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d136974 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
    | true =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
  have h13 (q : Pattern) (ha : d137084 q = 1) (hb : d138215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137084, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d137084, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137087 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137088 q = 1) (hb : d138216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137088, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137088, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137089 q = 1) (hb : d138217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137089, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d137089, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137090 q = 1) (hb : d138218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137090, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d137090, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137091 q = 1) (hb : d138219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137091, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137091, d138219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24622 (p : Pattern) (ha : d137100 p = 1) (hb : d139273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136974 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24373 q ha hb
    | true =>
      simp only [d136974, d138158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24357 q ha hb
  have h3 (q : Pattern) (ha : d137084 q = 1) (hb : d138215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137084, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137084, d138215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137087 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137088 q = 1) (hb : d138216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137088, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137088, d138216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137098 q = 1) (hb : d138217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137098, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137098, d138217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137099 q = 1) (hb : d138218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137099, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137099, d138218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137100 q = 1) (hb : d139273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137100, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137100, d139273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24623 (p : Pattern) (ha : d137130 p = 1) (hb : d139283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137005 q = 1) (hb : d138190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137005, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24378 q ha hb
    | true =>
      simp only [d137005, d138190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24361 q ha hb
  have h3 (q : Pattern) (ha : d137120 q = 1) (hb : d139279 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137120, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137120, d139279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137127 q = 1) (hb : d139280 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137127, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137127, d139280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137128 q = 1) (hb : d139281 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137128, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137128, d139281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137129 q = 1) (hb : d139282 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137129, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137129, d139282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137130 q = 1) (hb : d139283 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137130, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137130, d139283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24624 (p : Pattern) (ha : d137142 p = 1) (hb : d139289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137037 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137092 q = 1) (hb : d138220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137092, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24620 q ha hb
    | true =>
      simp only [d137092, d138220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24621 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137095 q = 1) (hb : d138221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137095, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137095, d138221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137096 q = 1) (hb : d139271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137096, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137096, d139271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137097 q = 1) (hb : d139272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137097, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137097, d139272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137101 q = 1) (hb : d139274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137101, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137101, d139274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24622 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137103 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137104 q = 1) (hb : d139275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137104, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137104, d139275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d137105 q = 1) (hb : d139276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137105, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137105, d139276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d137106 q = 1) (hb : d139277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137106, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137106, d139277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d137107 q = 1) (hb : d139278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137107, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137107, d139278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137131 q = 1) (hb : d139284 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137131, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137131, d139284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24623 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137138 q = 1) (hb : d139285 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137138, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137138, d139285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137139 q = 1) (hb : d139286 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137139, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137139, d139286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137140 q = 1) (hb : d139287 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137140, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137140, d139287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d137141 q = 1) (hb : d139288 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137141, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137141, d139288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d137142 q = 1) (hb : d139289 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137142, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137142, d139289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24625 (p : Pattern) (ha : d137148 p = 1) (hb : d139295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137143 q = 1) (hb : d139290 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137143, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137143, d139290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24624 q ha hb
  have h2 (q : Pattern) (ha : d137144 q = 1) (hb : d139291 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137144, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137144, d139291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137145 q = 1) (hb : d139292 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137145, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137145, d139292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137146 q = 1) (hb : d139293 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137146, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137146, d139293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137147 q = 1) (hb : d139294 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137147, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137147, d139294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137148 q = 1) (hb : d139295 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137148, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137148, d139295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24626 (p : Pattern) (ha : d137237 p = 1) (hb : d138366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137207 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d137219 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137172 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
    | true =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
  have h5 (q : Pattern) (ha : d137220 q = 1) (hb : d138362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137220, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d137220, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137233 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137234 q = 1) (hb : d138363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137234, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137234, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137235 q = 1) (hb : d138364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137235, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137235, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137236 q = 1) (hb : d138365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137236, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137236, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137237 q = 1) (hb : d138366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137237, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137237, d138366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24627 (p : Pattern) (ha : d137258 p = 1) (hb : d138376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137198 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137172 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24407 q ha hb
    | true =>
      simp only [d137172, d138361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24408 q ha hb
  have h4 (q : Pattern) (ha : d137220 q = 1) (hb : d138362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137220, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137220, d138362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137233 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137234 q = 1) (hb : d138363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137234, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137234, d138363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137235 q = 1) (hb : d138364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137235, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137235, d138364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137236 q = 1) (hb : d138365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137236, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137236, d138365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137243 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137248 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d137250 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d137182 q = 1) (hb : d138371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24410 q ha hb
    | true =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24411 q ha hb
  have h13 (q : Pattern) (ha : d137251 q = 1) (hb : d138372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137251, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d137251, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137254 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137255 q = 1) (hb : d138373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137255, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137255, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137256 q = 1) (hb : d138374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137256, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d137256, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137257 q = 1) (hb : d138375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137257, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d137257, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137258 q = 1) (hb : d138376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137258, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137258, d138376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24628 (p : Pattern) (ha : d137278 p = 1) (hb : d139299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137250 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137182 q = 1) (hb : d138371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24410 q ha hb
    | true =>
      simp only [d137182, d138371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24411 q ha hb
  have h3 (q : Pattern) (ha : d137251 q = 1) (hb : d138372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137251, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137251, d138372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137254 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137255 q = 1) (hb : d138373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137255, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137255, d138373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137276 q = 1) (hb : d138374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137276, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137276, d138374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137277 q = 1) (hb : d138375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137277, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137277, d138375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137278 q = 1) (hb : d139299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137278, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137278, d139299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24629 (p : Pattern) (ha : d137338 p = 1) (hb : d139310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137320 q = 1) (hb : d139305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137320, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24438 q ha hb
    | true =>
      simp only [d137320, d139305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24443 q ha hb
  have h3 (q : Pattern) (ha : d137321 q = 1) (hb : d139306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137321, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137321, d139306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137334 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137335 q = 1) (hb : d139307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137335, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137335, d139307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137336 q = 1) (hb : d139308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137336, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137336, d139308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137337 q = 1) (hb : d139309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137337, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137337, d139309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137338 q = 1) (hb : d139310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137338, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137338, d139310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24630 (p : Pattern) (ha : d137351 p = 1) (hb : d139316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137259 q = 1) (hb : d138377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137259, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24626 q ha hb
    | true =>
      simp only [d137259, d138377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24627 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137272 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137273 q = 1) (hb : d138378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137273, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137273, d138378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137274 q = 1) (hb : d139297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137274, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137274, d139297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137275 q = 1) (hb : d139298 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137275, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137275, d139298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137279 q = 1) (hb : d139300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137279, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137279, d139300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24628 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137281 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137282 q = 1) (hb : d139301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137282, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137282, d139301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d137283 q = 1) (hb : d139302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137283, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137283, d139302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d137284 q = 1) (hb : d139303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137284, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137284, d139303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d137285 q = 1) (hb : d139304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137285, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137285, d139304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137339 q = 1) (hb : d139311 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137339, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137339, d139311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24629 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137347 q = 1) (hb : d139312 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137347, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137347, d139312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137348 q = 1) (hb : d139313 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137348, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137348, d139313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137349 q = 1) (hb : d139314 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137349, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137349, d139314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d137350 q = 1) (hb : d139315 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137350, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137350, d139315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d137351 q = 1) (hb : d139316 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137351, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137351, d139316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24631 (p : Pattern) (ha : d137357 p = 1) (hb : d139322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137352 q = 1) (hb : d139317 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137352, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137352, d139317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24630 q ha hb
  have h2 (q : Pattern) (ha : d137353 q = 1) (hb : d139318 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137353, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137353, d139318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137354 q = 1) (hb : d139319 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137354, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137354, d139319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137355 q = 1) (hb : d139320 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137355, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137355, d139320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137356 q = 1) (hb : d139321 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137356, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137356, d139321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137357 q = 1) (hb : d139322 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137357, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137357, d139322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24632 (p : Pattern) (ha : d137447 p = 1) (hb : d138583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137417 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d137429 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137382 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
    | true =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
  have h5 (q : Pattern) (ha : d137430 q = 1) (hb : d138579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137430, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d137430, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137443 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137444 q = 1) (hb : d138580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137444, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137444, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137445 q = 1) (hb : d138581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137445, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137445, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137446 q = 1) (hb : d138582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137446, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137446, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137447 q = 1) (hb : d138583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137447, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137447, d138583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24633 (p : Pattern) (ha : d137468 p = 1) (hb : d138593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137408 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137417 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137382 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24449 q ha hb
    | true =>
      simp only [d137382, d138578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24450 q ha hb
  have h4 (q : Pattern) (ha : d137430 q = 1) (hb : d138579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137430, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137430, d138579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137443 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137444 q = 1) (hb : d138580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137444, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137444, d138580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137445 q = 1) (hb : d138581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137445, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137445, d138581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137446 q = 1) (hb : d138582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137446, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137446, d138582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137453 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137458 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d137460 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d137392 q = 1) (hb : d138588 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24452 q ha hb
    | true =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24453 q ha hb
  have h13 (q : Pattern) (ha : d137461 q = 1) (hb : d138589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137461, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d137461, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137464 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137465 q = 1) (hb : d138590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137465, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137465, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137466 q = 1) (hb : d138591 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137466, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d137466, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137467 q = 1) (hb : d138592 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137467, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d137467, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137468 q = 1) (hb : d138593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137468, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137468, d138593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24634 (p : Pattern) (ha : d137488 p = 1) (hb : d139327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137460 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137392 q = 1) (hb : d138588 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24452 q ha hb
    | true =>
      simp only [d137392, d138588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24453 q ha hb
  have h3 (q : Pattern) (ha : d137461 q = 1) (hb : d138589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137461, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137461, d138589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137465 q = 1) (hb : d138590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137465, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137465, d138590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137486 q = 1) (hb : d138591 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137486, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137486, d138591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137487 q = 1) (hb : d138592 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137487, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137487, d138592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137488 q = 1) (hb : d139327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137488, d139327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137488, d139327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24635 (p : Pattern) (ha : d137548 p = 1) (hb : d139338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137530 q = 1) (hb : d139333 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137530, d139333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24480 q ha hb
    | true =>
      simp only [d137530, d139333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24485 q ha hb
  have h3 (q : Pattern) (ha : d137531 q = 1) (hb : d139334 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137531, d139334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137531, d139334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137545 q = 1) (hb : d139335 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137545, d139335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137545, d139335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137546 q = 1) (hb : d139336 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137546, d139336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137546, d139336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137547 q = 1) (hb : d139337 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137547, d139337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137547, d139337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137548 q = 1) (hb : d139338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137548, d139338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137548, d139338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24636 (p : Pattern) (ha : d137561 p = 1) (hb : d139344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137400 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137469 q = 1) (hb : d138594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137469, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24632 q ha hb
    | true =>
      simp only [d137469, d138594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24633 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137483 q = 1) (hb : d138595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137483, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137483, d138595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137484 q = 1) (hb : d139325 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137484, d139325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137484, d139325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137485 q = 1) (hb : d139326 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137485, d139326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137485, d139326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137489 q = 1) (hb : d139328 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137489, d139328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137489, d139328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24634 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137492 q = 1) (hb : d139329 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137492, d139329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137492, d139329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d137493 q = 1) (hb : d139330 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137493, d139330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137493, d139330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d137494 q = 1) (hb : d139331 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137494, d139331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137494, d139331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d137495 q = 1) (hb : d139332 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137495, d139332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137495, d139332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137549 q = 1) (hb : d139339 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137549, d139339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137549, d139339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24635 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137556 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137557 q = 1) (hb : d139340 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137557, d139340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137557, d139340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137558 q = 1) (hb : d139341 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137558, d139341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137558, d139341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137559 q = 1) (hb : d139342 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137559, d139342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137559, d139342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d137560 q = 1) (hb : d139343 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137560, d139343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137560, d139343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d137561 q = 1) (hb : d139344 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137561, d139344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137561, d139344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24637 (p : Pattern) (ha : d137567 p = 1) (hb : d139350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137562 q = 1) (hb : d139345 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137562, d139345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137562, d139345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24636 q ha hb
  have h2 (q : Pattern) (ha : d137563 q = 1) (hb : d139346 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137563, d139346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137563, d139346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137564 q = 1) (hb : d139347 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137564, d139347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137564, d139347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137565 q = 1) (hb : d139348 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137565, d139348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137565, d139348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137566 q = 1) (hb : d139349 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137566, d139349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137566, d139349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137567 q = 1) (hb : d139350 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137567, d139350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137567, d139350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24638 (p : Pattern) (ha : d137658 p = 1) (hb : d138801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d137640 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137593 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
    | true =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
  have h5 (q : Pattern) (ha : d137641 q = 1) (hb : d138797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137641, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d137641, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137654 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137655 q = 1) (hb : d138798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137655, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137655, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137656 q = 1) (hb : d138799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137656, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137656, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137657 q = 1) (hb : d138800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137657, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137657, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137658 q = 1) (hb : d138801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137658, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137658, d138801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24639 (p : Pattern) (ha : d137679 p = 1) (hb : d138811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137619 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137640 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137593 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24491 q ha hb
    | true =>
      simp only [d137593, d138796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24492 q ha hb
  have h4 (q : Pattern) (ha : d137641 q = 1) (hb : d138797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137641, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137641, d138797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137654 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137655 q = 1) (hb : d138798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137655, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137655, d138798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137656 q = 1) (hb : d138799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137656, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137656, d138799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137657 q = 1) (hb : d138800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137657, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137657, d138800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137664 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137669 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d137671 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d137603 q = 1) (hb : d138806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24494 q ha hb
    | true =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24495 q ha hb
  have h13 (q : Pattern) (ha : d137672 q = 1) (hb : d138807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137672, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d137672, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137676 q = 1) (hb : d138808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137676, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137676, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137677 q = 1) (hb : d138809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137677, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d137677, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137678 q = 1) (hb : d138810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137678, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d137678, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137679 q = 1) (hb : d138811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137679, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137679, d138811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24640 (p : Pattern) (ha : d137699 p = 1) (hb : d139356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137671 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137603 q = 1) (hb : d138806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24494 q ha hb
    | true =>
      simp only [d137603, d138806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24495 q ha hb
  have h3 (q : Pattern) (ha : d137672 q = 1) (hb : d138807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137672, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137672, d138807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137675 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137676 q = 1) (hb : d138808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137676, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137676, d138808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137697 q = 1) (hb : d138809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137697, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137697, d138809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137698 q = 1) (hb : d138810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137698, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137698, d138810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137699 q = 1) (hb : d139356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137699, d139356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137699, d139356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24641 (p : Pattern) (ha : d137759 p = 1) (hb : d139367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137741 q = 1) (hb : d139362 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137741, d139362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24522 q ha hb
    | true =>
      simp only [d137741, d139362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24527 q ha hb
  have h3 (q : Pattern) (ha : d137742 q = 1) (hb : d139363 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137742, d139363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137742, d139363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137755 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137756 q = 1) (hb : d139364 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137756, d139364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137756, d139364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137757 q = 1) (hb : d139365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137757, d139365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137757, d139365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137758 q = 1) (hb : d139366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137758, d139366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137758, d139366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137759 q = 1) (hb : d139367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137759, d139367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137759, d139367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24642 (p : Pattern) (ha : d137772 p = 1) (hb : d139373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137611 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137680 q = 1) (hb : d138812 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137680, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24638 q ha hb
    | true =>
      simp only [d137680, d138812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24639 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137694 q = 1) (hb : d138813 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137694, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137694, d138813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137695 q = 1) (hb : d139354 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137695, d139354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137695, d139354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137696 q = 1) (hb : d139355 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137696, d139355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137696, d139355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137700 q = 1) (hb : d139357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137700, d139357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137700, d139357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24640 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137702 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137703 q = 1) (hb : d139358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137703, d139358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137703, d139358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d137704 q = 1) (hb : d139359 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137704, d139359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137704, d139359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d137705 q = 1) (hb : d139360 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137705, d139360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137705, d139360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d137706 q = 1) (hb : d139361 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137706, d139361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137706, d139361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137760 q = 1) (hb : d139368 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137760, d139368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137760, d139368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24641 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137768 q = 1) (hb : d139369 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137768, d139369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137768, d139369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137769 q = 1) (hb : d139370 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137769, d139370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137769, d139370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137770 q = 1) (hb : d139371 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137770, d139371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137770, d139371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d137771 q = 1) (hb : d139372 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137771, d139372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137771, d139372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d137772 q = 1) (hb : d139373 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137772, d139373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137772, d139373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24643 (p : Pattern) (ha : d137778 p = 1) (hb : d139379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137773 q = 1) (hb : d139374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137773, d139374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137773, d139374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24642 q ha hb
  have h2 (q : Pattern) (ha : d137774 q = 1) (hb : d139375 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137774, d139375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137774, d139375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137775 q = 1) (hb : d139376 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137775, d139376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137775, d139376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137776 q = 1) (hb : d139377 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137776, d139377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137776, d139377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137777 q = 1) (hb : d139378 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137777, d139378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137777, d139378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137778 q = 1) (hb : d139379 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137778, d139379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137778, d139379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24644 (p : Pattern) (ha : d137870 p = 1) (hb : d139020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137831 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d137852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137805 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
    | true =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
  have h5 (q : Pattern) (ha : d137853 q = 1) (hb : d139016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137853, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d137853, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137866 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d137867 q = 1) (hb : d139017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137867, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137867, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d137868 q = 1) (hb : d139018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137868, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137868, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137869 q = 1) (hb : d139019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137869, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137869, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137870 q = 1) (hb : d139020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137870, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137870, d139020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24645 (p : Pattern) (ha : d137891 p = 1) (hb : d139030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137831 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137805 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24533 q ha hb
    | true =>
      simp only [d137805, d139015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24534 q ha hb
  have h4 (q : Pattern) (ha : d137853 q = 1) (hb : d139016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137853, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d137853, d139016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137866 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d137867 q = 1) (hb : d139017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137867, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137867, d139017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137868 q = 1) (hb : d139018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137868, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137868, d139018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137869 q = 1) (hb : d139019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137869, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137869, d139019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137876 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137881 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d137883 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d137815 q = 1) (hb : d139025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24536 q ha hb
    | true =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24537 q ha hb
  have h13 (q : Pattern) (ha : d137884 q = 1) (hb : d139026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137884, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d137884, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137887 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137888 q = 1) (hb : d139027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137888, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137888, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137889 q = 1) (hb : d139028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137889, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d137889, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d137890 q = 1) (hb : d139029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137890, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d137890, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137891 q = 1) (hb : d139030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137891, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d137891, d139030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24646 (p : Pattern) (ha : d137911 p = 1) (hb : d139386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137815 q = 1) (hb : d139025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24536 q ha hb
    | true =>
      simp only [d137815, d139025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24537 q ha hb
  have h3 (q : Pattern) (ha : d137884 q = 1) (hb : d139026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137884, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137884, d139026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137887 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137888 q = 1) (hb : d139027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137888, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137888, d139027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137909 q = 1) (hb : d139028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137909, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137909, d139028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137910 q = 1) (hb : d139029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137910, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137910, d139029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137911 q = 1) (hb : d139386 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137911, d139386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137911, d139386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24647 (p : Pattern) (ha : d137971 p = 1) (hb : d139397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137948 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137953 q = 1) (hb : d139392 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137953, d139392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24564 q ha hb
    | true =>
      simp only [d137953, d139392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24569 q ha hb
  have h3 (q : Pattern) (ha : d137954 q = 1) (hb : d139393 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137954, d139393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137954, d139393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137968 q = 1) (hb : d139394 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137968, d139394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137968, d139394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137969 q = 1) (hb : d139395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137969, d139395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137969, d139395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137970 q = 1) (hb : d139396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137970, d139396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137970, d139396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137971 q = 1) (hb : d139397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137971, d139397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137971, d139397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24648 (p : Pattern) (ha : d137984 p = 1) (hb : d139403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137823 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137892 q = 1) (hb : d139031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137892, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24644 q ha hb
    | true =>
      simp only [d137892, d139031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24645 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137905 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137906 q = 1) (hb : d139032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137906, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137906, d139032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d137907 q = 1) (hb : d139384 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137907, d139384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137907, d139384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137908 q = 1) (hb : d139385 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137908, d139385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137908, d139385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137912 q = 1) (hb : d139387 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137912, d139387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137912, d139387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24646 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137914 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137915 q = 1) (hb : d139388 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137915, d139388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137915, d139388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d137916 q = 1) (hb : d139389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137916, d139389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d137916, d139389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d137917 q = 1) (hb : d139390 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137917, d139390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137917, d139390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d137918 q = 1) (hb : d139391 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137918, d139391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137918, d139391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137972 q = 1) (hb : d139398 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137972, d139398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d137972, d139398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24647 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137979 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d137980 q = 1) (hb : d139399 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137980, d139399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137980, d139399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d137981 q = 1) (hb : d139400 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137981, d139400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137981, d139400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d137982 q = 1) (hb : d139401 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137982, d139401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137982, d139401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d137983 q = 1) (hb : d139402 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137983, d139402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137983, d139402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d137984 q = 1) (hb : d139403 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137984, d139403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137984, d139403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24649 (p : Pattern) (ha : d137990 p = 1) (hb : d139409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137985 q = 1) (hb : d139404 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137985, d139404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137985, d139404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24648 q ha hb
  have h2 (q : Pattern) (ha : d137986 q = 1) (hb : d139405 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137986, d139405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137986, d139405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137987 q = 1) (hb : d139406 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137987, d139406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137987, d139406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137988 q = 1) (hb : d139407 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137988, d139407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137988, d139407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137989 q = 1) (hb : d139408 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137989, d139408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137989, d139408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137990 q = 1) (hb : d139409 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137990, d139409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137990, d139409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24650 (p : Pattern) (ha : d137996 p = 1) (hb : d139415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d137149 q = 1) (hb : d139296 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137149, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24619 q ha hb
    | true =>
      simp only [d137149, d139296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24625 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137358 q = 1) (hb : d139323 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137358, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137358, d139323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24631 q ha hb
  have h3 (q : Pattern) (ha : d137359 q = 1) (hb : d139324 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137359, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d137359, d139324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137568 q = 1) (hb : d139351 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137568, d139351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137568, d139351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24637 q ha hb
  have h5 (q : Pattern) (ha : d137569 q = 1) (hb : d139352 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137569, d139352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137569, d139352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137570 q = 1) (hb : d139353 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137570, d139353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137570, d139353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137779 q = 1) (hb : d139380 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137779, d139380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137779, d139380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24643 q ha hb
  have h8 (q : Pattern) (ha : d137780 q = 1) (hb : d139381 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137780, d139381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137780, d139381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137781 q = 1) (hb : d139382 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137781, d139382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137781, d139382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137782 q = 1) (hb : d139383 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d137782, d139383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137782, d139383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137991 q = 1) (hb : d139410 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d137991, d139410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137991, d139410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24649 q ha hb
  have h12 (q : Pattern) (ha : d137992 q = 1) (hb : d139411 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d137992, d139411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137992, d139411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137993 q = 1) (hb : d139412 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d137993, d139412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137993, d139412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137994 q = 1) (hb : d139413 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d137994, d139413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d137994, d139413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d137995 q = 1) (hb : d139414 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d137995, d139414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d137995, d139414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137996 q = 1) (hb : d139415 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d137996, d139415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137996, d139415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro24651 (p : Pattern) (ha : d138002 p = 1) (hb : d139421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137997 q = 1) (hb : d139416 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d137997, d139416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24650 q ha hb
    | true =>
      simp only [d137997, d139416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137998 q = 1) (hb : d139417 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d137998, d139417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137998, d139417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d137999 q = 1) (hb : d139418 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d137999, d139418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137999, d139418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138000 q = 1) (hb : d139419 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d138000, d139419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138000, d139419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138001 q = 1) (hb : d139420 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d138001, d139420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138001, d139420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138002 q = 1) (hb : d139421 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d138002, d139421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138002, d139421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24652 (p : Pattern) (ha : d138008 p = 1) (hb : d139427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138003 q = 1) (hb : d139422 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d138003, d139422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24651 q ha hb
    | true =>
      simp only [d138003, d139422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138004 q = 1) (hb : d139423 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d138004, d139423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138004, d139423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138005 q = 1) (hb : d139424 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d138005, d139424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138005, d139424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138006 q = 1) (hb : d139425 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d138006, d139425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138006, d139425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138007 q = 1) (hb : d139426 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d138007, d139426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138007, d139426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138008 q = 1) (hb : d139427 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d138008, d139427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138008, d139427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24653 (p : Pattern) (ha : d138014 p = 1) (hb : d139433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138009 q = 1) (hb : d139428 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d138009, d139428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24652 q ha hb
    | true =>
      simp only [d138009, d139428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138010 q = 1) (hb : d139429 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d138010, d139429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138010, d139429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138011 q = 1) (hb : d139430 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d138011, d139430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138011, d139430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138012 q = 1) (hb : d139431 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d138012, d139431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138012, d139431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138013 q = 1) (hb : d139432 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d138013, d139432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138013, d139432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138014 q = 1) (hb : d139433 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d138014, d139433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138014, d139433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24654 (p : Pattern) (ha : d138020 p = 1) (hb : d139439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138015 q = 1) (hb : d139434 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d138015, d139434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24653 q ha hb
    | true =>
      simp only [d138015, d139434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138016 q = 1) (hb : d139435 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d138016, d139435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138016, d139435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138017 q = 1) (hb : d139436 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d138017, d139436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138017, d139436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138018 q = 1) (hb : d139437 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d138018, d139437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138018, d139437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138019 q = 1) (hb : d139438 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d138019, d139438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138019, d139438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138020 q = 1) (hb : d139439 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d138020, d139439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138020, d139439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24655 (p : Pattern) (ha : d138026 p = 1) (hb : d139445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138021 q = 1) (hb : d139440 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d138021, d139440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24654 q ha hb
    | true =>
      simp only [d138021, d139440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138022 q = 1) (hb : d139441 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d138022, d139441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138022, d139441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138023 q = 1) (hb : d139442 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d138023, d139442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138023, d139442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138024 q = 1) (hb : d139443 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d138024, d139443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138024, d139443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138025 q = 1) (hb : d139444 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d138025, d139444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138025, d139444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138026 q = 1) (hb : d139445 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d138026, d139445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138026, d139445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24656 (p : Pattern) (ha : d138032 p = 1) (hb : d139451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138027 q = 1) (hb : d139446 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d138027, d139446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24655 q ha hb
    | true =>
      simp only [d138027, d139446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138028 q = 1) (hb : d139447 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d138028, d139447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138028, d139447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138029 q = 1) (hb : d139448 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d138029, d139448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138029, d139448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138030 q = 1) (hb : d139449 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d138030, d139449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138030, d139449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138031 q = 1) (hb : d139450 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d138031, d139450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138031, d139450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138032 q = 1) (hb : d139451 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d138032, d139451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138032, d139451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24657 (p : Pattern) (ha : d138038 p = 1) (hb : d139457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138033 q = 1) (hb : d139452 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d138033, d139452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24656 q ha hb
    | true =>
      simp only [d138033, d139452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d138034 q = 1) (hb : d139453 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d138034, d139453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138034, d139453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d138035 q = 1) (hb : d139454 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d138035, d139454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138035, d139454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d138036 q = 1) (hb : d139455 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d138036, d139455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138036, d139455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d138037 q = 1) (hb : d139456 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d138037, d139456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138037, d139456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d138038 q = 1) (hb : d139457 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d138038, d139457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138038, d139457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro24658 (p : Pattern) (ha : d138107 p = 1) (hb : d139462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135521 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d135533 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138103 q = 1) (hb : d139458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138103, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138103, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135445 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d138104 q = 1) (hb : d139459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138104, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138104, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138105 q = 1) (hb : d139460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138105, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138105, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d138106 q = 1) (hb : d139461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138106, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138106, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d138107 q = 1) (hb : d139462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138107, d139462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138107, d139462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24659 (p : Pattern) (ha : d138114 p = 1) (hb : d139467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135533 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d138051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d138103 q = 1) (hb : d139458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138103, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138103, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135445 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138104 q = 1) (hb : d139459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138104, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138104, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138105 q = 1) (hb : d139460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138105, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138105, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138106 q = 1) (hb : d139461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138106, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138106, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135555 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135559 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d135561 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d138110 q = 1) (hb : d139463 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138110, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d138110, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d138111 q = 1) (hb : d139464 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138111, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d138111, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d138112 q = 1) (hb : d139465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138112, d139465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d138112, d139465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d138113 q = 1) (hb : d139466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138113, d139466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138113, d139466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d138114 q = 1) (hb : d139467 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138114, d139467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138114, d139467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24660 (p : Pattern) (ha : d138288 p = 1) (hb : d139474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138058 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138110 q = 1) (hb : d139463 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138110, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138110, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138111 q = 1) (hb : d139464 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138111, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138111, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138112 q = 1) (hb : d139472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138112, d139472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138112, d139472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138113 q = 1) (hb : d139473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138113, d139473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138113, d139473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138288 q = 1) (hb : d139474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138288, d139474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138288, d139474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24661 (p : Pattern) (ha : d138323 p = 1) (hb : d139484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138319 q = 1) (hb : d139480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138319, d139480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138319, d139480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135479 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138320 q = 1) (hb : d139481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138320, d139481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138320, d139481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138321 q = 1) (hb : d139482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138321, d139482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138321, d139482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138322 q = 1) (hb : d139483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138322, d139483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138322, d139483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138323 q = 1) (hb : d139484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138323, d139484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138323, d139484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24662 (p : Pattern) (ha : d139264 p = 1) (hb : d139490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135509 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138115 q = 1) (hb : d139468 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138115, d139468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24658 q ha hb
    | true =>
      simp only [d138115, d139468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24659 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138116 q = 1) (hb : d139469 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d138116, d139469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138116, d139469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139254 q = 1) (hb : d139470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139254, d139470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139254, d139470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139255 q = 1) (hb : d139471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139255, d139471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139255, d139471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138289 q = 1) (hb : d139475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138289, d139475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138289, d139475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24660 q ha hb
  have h8 (q : Pattern) (ha : d139256 q = 1) (hb : d139476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139256, d139476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139256, d139476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d139257 q = 1) (hb : d139477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139257, d139477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d139257, d139477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d139258 q = 1) (hb : d139478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139258, d139478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139258, d139478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139259 q = 1) (hb : d139479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139259, d139479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139259, d139479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d138324 q = 1) (hb : d139485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138324, d139485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138324, d139485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24661 q ha hb
  have h13 (q : Pattern) (ha : d139260 q = 1) (hb : d139486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139260, d139486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139260, d139486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d139261 q = 1) (hb : d139487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139261, d139487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139261, d139487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d139262 q = 1) (hb : d139488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139262, d139488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d139262, d139488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d139263 q = 1) (hb : d139489 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139263, d139489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139263, d139489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139264 q = 1) (hb : d139490 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139264, d139490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d139264, d139490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24663 (p : Pattern) (ha : d139270 p = 1) (hb : d139496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139265 q = 1) (hb : d139491 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139265, d139491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139265, d139491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24662 q ha hb
  have h3 (q : Pattern) (ha : d139266 q = 1) (hb : d139492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139266, d139492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139266, d139492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139267 q = 1) (hb : d139493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139267, d139493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139267, d139493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139268 q = 1) (hb : d139494 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139268, d139494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139268, d139494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139269 q = 1) (hb : d139495 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139269, d139495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139269, d139495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139270 q = 1) (hb : d139496 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139270, d139496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139270, d139496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24664 (p : Pattern) (ha : d138212 p = 1) (hb : d139501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135650 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d135662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138208 q = 1) (hb : d139497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138208, d139497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138208, d139497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135681 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d138209 q = 1) (hb : d139498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138209, d139498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138209, d139498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138210 q = 1) (hb : d139499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138210, d139499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138210, d139499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d138211 q = 1) (hb : d139500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138211, d139500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138211, d139500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d138212 q = 1) (hb : d139501 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138212, d139501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138212, d139501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24665 (p : Pattern) (ha : d138219 p = 1) (hb : d139506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135644 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135662 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d138142 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d138208 q = 1) (hb : d139497 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138208, d139497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138208, d139497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135681 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138209 q = 1) (hb : d139498 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138209, d139498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138209, d139498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138210 q = 1) (hb : d139499 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138210, d139499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138210, d139499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138211 q = 1) (hb : d139500 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138211, d139500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138211, d139500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135690 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d135696 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d138215 q = 1) (hb : d139502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138215, d139502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d138215, d139502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135702 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d138216 q = 1) (hb : d139503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138216, d139503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d138216, d139503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d138217 q = 1) (hb : d139504 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138217, d139504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d138217, d139504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d138218 q = 1) (hb : d139505 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138218, d139505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138218, d139505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d138219 q = 1) (hb : d139506 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138219, d139506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138219, d139506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24666 (p : Pattern) (ha : d139273 p = 1) (hb : d139513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138215 q = 1) (hb : d139502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138215, d139502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138215, d139502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135702 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138216 q = 1) (hb : d139503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138216, d139503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138216, d139503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138217 q = 1) (hb : d139511 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138217, d139511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138217, d139511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138218 q = 1) (hb : d139512 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138218, d139512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138218, d139512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139273 q = 1) (hb : d139513 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139273, d139513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139273, d139513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24667 (p : Pattern) (ha : d139283 p = 1) (hb : d139523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138190 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139279 q = 1) (hb : d139519 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139279, d139519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139279, d139519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139280 q = 1) (hb : d139520 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139280, d139520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139280, d139520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139281 q = 1) (hb : d139521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139281, d139521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139281, d139521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139282 q = 1) (hb : d139522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139282, d139522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139282, d139522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139283 q = 1) (hb : d139523 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139283, d139523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139283, d139523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24668 (p : Pattern) (ha : d139289 p = 1) (hb : d139529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135638 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138220 q = 1) (hb : d139507 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138220, d139507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24664 q ha hb
    | true =>
      simp only [d138220, d139507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24665 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138221 q = 1) (hb : d139508 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d138221, d139508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138221, d139508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139271 q = 1) (hb : d139509 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139271, d139509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139271, d139509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139272 q = 1) (hb : d139510 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139272, d139510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139272, d139510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139274 q = 1) (hb : d139514 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139274, d139514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139274, d139514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24666 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d135718 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d139275 q = 1) (hb : d139515 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139275, d139515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139275, d139515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139276 q = 1) (hb : d139516 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139276, d139516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139276, d139516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139277 q = 1) (hb : d139517 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139277, d139517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139277, d139517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d139278 q = 1) (hb : d139518 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139278, d139518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139278, d139518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139284 q = 1) (hb : d139524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139284, d139524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139284, d139524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24667 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135764 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139285 q = 1) (hb : d139525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139285, d139525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139285, d139525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139286 q = 1) (hb : d139526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139286, d139526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139286, d139526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139287 q = 1) (hb : d139527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139287, d139527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d139287, d139527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d139288 q = 1) (hb : d139528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139288, d139528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d139288, d139528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d139289 q = 1) (hb : d139529 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139289, d139529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139289, d139529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24669 (p : Pattern) (ha : d139295 p = 1) (hb : d139535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139290 q = 1) (hb : d139530 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139290, d139530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139290, d139530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24668 q ha hb
  have h2 (q : Pattern) (ha : d139291 q = 1) (hb : d139531 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139291, d139531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139291, d139531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d139292 q = 1) (hb : d139532 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139292, d139532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139292, d139532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139293 q = 1) (hb : d139533 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139293, d139533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139293, d139533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139294 q = 1) (hb : d139534 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139294, d139534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139294, d139534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139295 q = 1) (hb : d139535 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139295, d139535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139295, d139535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24670 (p : Pattern) (ha : d138366 p = 1) (hb : d139541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d135846 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138362 q = 1) (hb : d139537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138362, d139537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138362, d139537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135883 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d138363 q = 1) (hb : d139538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138363, d139538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138363, d139538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138364 q = 1) (hb : d139539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138364, d139539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138364, d139539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d138365 q = 1) (hb : d139540 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138365, d139540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138365, d139540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d138366 q = 1) (hb : d139541 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138366, d139541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138366, d139541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24671 (p : Pattern) (ha : d138376 p = 1) (hb : d139546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d138361 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d138362 q = 1) (hb : d139537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138362, d139537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138362, d139537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135883 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138363 q = 1) (hb : d139538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138363, d139538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138363, d139538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138364 q = 1) (hb : d139539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138364, d139539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138364, d139539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138365 q = 1) (hb : d139540 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138365, d139540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138365, d139540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135893 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135898 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d135900 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d138371 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d138372 q = 1) (hb : d139542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138372, d139542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d138372, d139542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135907 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d138373 q = 1) (hb : d139543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138373, d139543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d138373, d139543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d138374 q = 1) (hb : d139544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138374, d139544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d138374, d139544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d138375 q = 1) (hb : d139545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138375, d139545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138375, d139545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d138376 q = 1) (hb : d139546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138376, d139546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138376, d139546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24672 (p : Pattern) (ha : d139299 p = 1) (hb : d139553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138372 q = 1) (hb : d139542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138372, d139542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138372, d139542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135907 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138373 q = 1) (hb : d139543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138373, d139543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138373, d139543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138374 q = 1) (hb : d139551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138374, d139551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138374, d139551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138375 q = 1) (hb : d139552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138375, d139552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138375, d139552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139299 q = 1) (hb : d139553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139299, d139553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139299, d139553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24673 (p : Pattern) (ha : d139310 p = 1) (hb : d139563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139306 q = 1) (hb : d139559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139306, d139559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139306, d139559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136005 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139307 q = 1) (hb : d139560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139307, d139560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139307, d139560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139308 q = 1) (hb : d139561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139308, d139561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139308, d139561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139309 q = 1) (hb : d139562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139309, d139562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139309, d139562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139310 q = 1) (hb : d139563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139310, d139563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139310, d139563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24674 (p : Pattern) (ha : d139316 p = 1) (hb : d139569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138377 q = 1) (hb : d139547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138377, d139547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24670 q ha hb
    | true =>
      simp only [d138377, d139547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24671 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138378 q = 1) (hb : d139548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d138378, d139548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138378, d139548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139297 q = 1) (hb : d139549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139297, d139549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139297, d139549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139298 q = 1) (hb : d139550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139298, d139550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139298, d139550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139300 q = 1) (hb : d139554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139300, d139554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139300, d139554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24672 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d135934 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d139301 q = 1) (hb : d139555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139301, d139555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139301, d139555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139302 q = 1) (hb : d139556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139302, d139556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139302, d139556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139303 q = 1) (hb : d139557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139303, d139557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139303, d139557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d139304 q = 1) (hb : d139558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139304, d139558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139304, d139558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139311 q = 1) (hb : d139564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139311, d139564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139311, d139564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24673 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136021 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139312 q = 1) (hb : d139565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139312, d139565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139312, d139565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139313 q = 1) (hb : d139566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139313, d139566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139313, d139566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139314 q = 1) (hb : d139567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139314, d139567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d139314, d139567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d139315 q = 1) (hb : d139568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139315, d139568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d139315, d139568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d139316 q = 1) (hb : d139569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139316, d139569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139316, d139569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24675 (p : Pattern) (ha : d139322 p = 1) (hb : d139575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139317 q = 1) (hb : d139570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139317, d139570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139317, d139570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24674 q ha hb
  have h2 (q : Pattern) (ha : d139318 q = 1) (hb : d139571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139318, d139571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139318, d139571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d139319 q = 1) (hb : d139572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139319, d139572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139319, d139572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139320 q = 1) (hb : d139573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139320, d139573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139320, d139573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139321 q = 1) (hb : d139574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139321, d139574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139321, d139574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139322 q = 1) (hb : d139575 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139322, d139575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139322, d139575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24676 (p : Pattern) (ha : d138583 p = 1) (hb : d139582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d136104 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138579 q = 1) (hb : d139578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138579, d139578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138579, d139578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136141 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d138580 q = 1) (hb : d139579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138580, d139579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138580, d139579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138581 q = 1) (hb : d139580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138581, d139580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138581, d139580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d138582 q = 1) (hb : d139581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138582, d139581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138582, d139581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d138583 q = 1) (hb : d139582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138583, d139582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138583, d139582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24677 (p : Pattern) (ha : d138593 p = 1) (hb : d139587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d138578 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d138579 q = 1) (hb : d139578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138579, d139578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138579, d139578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d136141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138580 q = 1) (hb : d139579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138580, d139579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138580, d139579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138581 q = 1) (hb : d139580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138581, d139580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138581, d139580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138582 q = 1) (hb : d139581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138582, d139581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138582, d139581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136151 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d136156 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d136158 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d138588 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d138589 q = 1) (hb : d139583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138589, d139583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d138589, d139583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d138590 q = 1) (hb : d139584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138590, d139584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d138590, d139584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d138591 q = 1) (hb : d139585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138591, d139585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d138591, d139585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d138592 q = 1) (hb : d139586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138592, d139586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138592, d139586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d138593 q = 1) (hb : d139587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138593, d139587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138593, d139587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24678 (p : Pattern) (ha : d139327 p = 1) (hb : d139594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138589 q = 1) (hb : d139583 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138589, d139583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138589, d139583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136165 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138590 q = 1) (hb : d139584 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138590, d139584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138590, d139584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138591 q = 1) (hb : d139592 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138591, d139592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138591, d139592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138592 q = 1) (hb : d139593 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138592, d139593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138592, d139593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139327 q = 1) (hb : d139594 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139327, d139594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139327, d139594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24679 (p : Pattern) (ha : d139338 p = 1) (hb : d139604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139334 q = 1) (hb : d139600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139334, d139600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139334, d139600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136263 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139335 q = 1) (hb : d139601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139335, d139601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139335, d139601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139336 q = 1) (hb : d139602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139336, d139602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139336, d139602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139337 q = 1) (hb : d139603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139337, d139603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139337, d139603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139338 q = 1) (hb : d139604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139338, d139604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139338, d139604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24680 (p : Pattern) (ha : d139344 p = 1) (hb : d139610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138594 q = 1) (hb : d139588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138594, d139588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24676 q ha hb
    | true =>
      simp only [d138594, d139588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24677 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136183 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138595 q = 1) (hb : d139589 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d138595, d139589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138595, d139589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139325 q = 1) (hb : d139590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139325, d139590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139325, d139590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139326 q = 1) (hb : d139591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139326, d139591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139326, d139591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139328 q = 1) (hb : d139595 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139328, d139595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139328, d139595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24678 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136192 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d139329 q = 1) (hb : d139596 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139329, d139596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139329, d139596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139330 q = 1) (hb : d139597 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139330, d139597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139330, d139597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139331 q = 1) (hb : d139598 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139331, d139598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139331, d139598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d139332 q = 1) (hb : d139599 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139332, d139599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139332, d139599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139339 q = 1) (hb : d139605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139339, d139605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139339, d139605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24679 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136279 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139340 q = 1) (hb : d139606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139340, d139606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139340, d139606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139341 q = 1) (hb : d139607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139341, d139607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139341, d139607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139342 q = 1) (hb : d139608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139342, d139608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d139342, d139608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d139343 q = 1) (hb : d139609 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139343, d139609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d139343, d139609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d139344 q = 1) (hb : d139610 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139344, d139610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139344, d139610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24681 (p : Pattern) (ha : d139350 p = 1) (hb : d139616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139345 q = 1) (hb : d139611 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139345, d139611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139345, d139611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24680 q ha hb
  have h2 (q : Pattern) (ha : d139346 q = 1) (hb : d139612 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139346, d139612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139346, d139612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d139347 q = 1) (hb : d139613 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139347, d139613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139347, d139613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139348 q = 1) (hb : d139614 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139348, d139614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139348, d139614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139349 q = 1) (hb : d139615 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139349, d139615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139349, d139615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139350 q = 1) (hb : d139616 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139350, d139616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139350, d139616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24682 (p : Pattern) (ha : d138801 p = 1) (hb : d139624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d136363 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138797 q = 1) (hb : d139620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138797, d139620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138797, d139620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136400 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d138798 q = 1) (hb : d139621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138798, d139621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d138798, d139621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138799 q = 1) (hb : d139622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138799, d139622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138799, d139622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d138800 q = 1) (hb : d139623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138800, d139623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138800, d139623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d138801 q = 1) (hb : d139624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138801, d139624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138801, d139624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24683 (p : Pattern) (ha : d138811 p = 1) (hb : d139629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136363 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d138796 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d138797 q = 1) (hb : d139620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138797, d139620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d138797, d139620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d136400 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d138798 q = 1) (hb : d139621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138798, d139621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d138798, d139621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138799 q = 1) (hb : d139622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138799, d139622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138799, d139622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d138800 q = 1) (hb : d139623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138800, d139623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138800, d139623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136410 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d136415 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d136417 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d138806 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d138807 q = 1) (hb : d139625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138807, d139625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d138807, d139625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136424 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d138808 q = 1) (hb : d139626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138808, d139626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d138808, d139626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d138809 q = 1) (hb : d139627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138809, d139627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d138809, d139627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d138810 q = 1) (hb : d139628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138810, d139628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138810, d139628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d138811 q = 1) (hb : d139629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d138811, d139629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138811, d139629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24684 (p : Pattern) (ha : d139356 p = 1) (hb : d139636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136417 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d138806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138807 q = 1) (hb : d139625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d138807, d139625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138807, d139625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136424 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d138808 q = 1) (hb : d139626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d138808, d139626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d138808, d139626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d138809 q = 1) (hb : d139634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d138809, d139634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138809, d139634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d138810 q = 1) (hb : d139635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d138810, d139635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d138810, d139635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139356 q = 1) (hb : d139636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139356, d139636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139356, d139636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24685 (p : Pattern) (ha : d139367 p = 1) (hb : d139646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136485 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139363 q = 1) (hb : d139642 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139363, d139642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139363, d139642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136522 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139364 q = 1) (hb : d139643 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139364, d139643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139364, d139643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139365 q = 1) (hb : d139644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139365, d139644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139365, d139644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139366 q = 1) (hb : d139645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139366, d139645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139366, d139645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139367 q = 1) (hb : d139646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139367, d139646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139367, d139646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24686 (p : Pattern) (ha : d139373 p = 1) (hb : d139652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d138812 q = 1) (hb : d139630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d138812, d139630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24682 q ha hb
    | true =>
      simp only [d138812, d139630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24683 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d138813 q = 1) (hb : d139631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d138813, d139631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d138813, d139631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139354 q = 1) (hb : d139632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139354, d139632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139354, d139632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139355 q = 1) (hb : d139633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139355, d139633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139355, d139633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139357 q = 1) (hb : d139637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139357, d139637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139357, d139637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24684 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d139358 q = 1) (hb : d139638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139358, d139638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139358, d139638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139359 q = 1) (hb : d139639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139359, d139639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139359, d139639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139360 q = 1) (hb : d139640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139360, d139640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139360, d139640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d139361 q = 1) (hb : d139641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139361, d139641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139361, d139641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139368 q = 1) (hb : d139647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139368, d139647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139368, d139647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24685 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136538 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139369 q = 1) (hb : d139648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139369, d139648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139369, d139648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139370 q = 1) (hb : d139649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139370, d139649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139370, d139649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139371 q = 1) (hb : d139650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139371, d139650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d139371, d139650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d139372 q = 1) (hb : d139651 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139372, d139651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d139372, d139651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d139373 q = 1) (hb : d139652 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139373, d139652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139373, d139652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24687 (p : Pattern) (ha : d139379 p = 1) (hb : d139658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139374 q = 1) (hb : d139653 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139374, d139653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139374, d139653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24686 q ha hb
  have h2 (q : Pattern) (ha : d139375 q = 1) (hb : d139654 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139375, d139654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139375, d139654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d139376 q = 1) (hb : d139655 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139376, d139655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139376, d139655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139377 q = 1) (hb : d139656 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139377, d139656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139377, d139656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139378 q = 1) (hb : d139657 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139378, d139657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139378, d139657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139379 q = 1) (hb : d139658 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139379, d139658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139379, d139658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24688 (p : Pattern) (ha : d139020 p = 1) (hb : d139667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136602 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d136623 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139016 q = 1) (hb : d139663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139016, d139663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139016, d139663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d139017 q = 1) (hb : d139664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139017, d139664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139017, d139664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139018 q = 1) (hb : d139665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139018, d139665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139018, d139665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d139019 q = 1) (hb : d139666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139019, d139666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139019, d139666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139020 q = 1) (hb : d139667 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139020, d139667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139020, d139667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24689 (p : Pattern) (ha : d139030 p = 1) (hb : d139672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136623 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d139015 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d139016 q = 1) (hb : d139663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139016, d139663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139016, d139663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d136660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d139017 q = 1) (hb : d139664 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139017, d139664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139017, d139664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139018 q = 1) (hb : d139665 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139018, d139665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139018, d139665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139019 q = 1) (hb : d139666 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139019, d139666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139019, d139666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d136675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d136677 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d139025 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d139026 q = 1) (hb : d139668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139026, d139668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d139026, d139668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136684 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139027 q = 1) (hb : d139669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139027, d139669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139027, d139669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139028 q = 1) (hb : d139670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139028, d139670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139028, d139670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d139029 q = 1) (hb : d139671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139029, d139671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139029, d139671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d139030 q = 1) (hb : d139672 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139030, d139672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d139030, d139672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro24690 (p : Pattern) (ha : d139386 p = 1) (hb : d139679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136677 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139026 q = 1) (hb : d139668 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139026, d139668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139026, d139668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136684 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139027 q = 1) (hb : d139669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139027, d139669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139027, d139669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139028 q = 1) (hb : d139677 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139028, d139677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139028, d139677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139029 q = 1) (hb : d139678 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139029, d139678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139029, d139678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139386 q = 1) (hb : d139679 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139386, d139679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139386, d139679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24691 (p : Pattern) (ha : d139397 p = 1) (hb : d139689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136745 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d139392 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139393 q = 1) (hb : d139685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d139393, d139685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139393, d139685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139394 q = 1) (hb : d139686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d139394, d139686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139394, d139686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139395 q = 1) (hb : d139687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d139395, d139687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139395, d139687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139396 q = 1) (hb : d139688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d139396, d139688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139396, d139688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d139397 q = 1) (hb : d139689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d139397, d139689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139397, d139689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24692 (p : Pattern) (ha : d139403 p = 1) (hb : d139695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139031 q = 1) (hb : d139673 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139031, d139673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24688 q ha hb
    | true =>
      simp only [d139031, d139673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24689 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d139032 q = 1) (hb : d139674 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139032, d139674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139032, d139674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d139384 q = 1) (hb : d139675 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139384, d139675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139384, d139675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139385 q = 1) (hb : d139676 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139385, d139676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139385, d139676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139387 q = 1) (hb : d139680 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139387, d139680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139387, d139680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24690 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136711 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d139388 q = 1) (hb : d139681 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139388, d139681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d139388, d139681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139389 q = 1) (hb : d139682 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139389, d139682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d139389, d139682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d139390 q = 1) (hb : d139683 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139390, d139683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139390, d139683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d139391 q = 1) (hb : d139684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139391, d139684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139391, d139684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139398 q = 1) (hb : d139690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d139398, d139690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139398, d139690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24691 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136798 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d139399 q = 1) (hb : d139691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d139399, d139691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d139399, d139691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139400 q = 1) (hb : d139692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d139400, d139692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139400, d139692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d139401 q = 1) (hb : d139693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d139401, d139693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d139401, d139693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d139402 q = 1) (hb : d139694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d139402, d139694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d139402, d139694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d139403 q = 1) (hb : d139695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d139403, d139695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d139403, d139695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24693 (p : Pattern) (ha : d139409 p = 1) (hb : d139701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139404 q = 1) (hb : d139696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d139404, d139696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139404, d139696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24692 q ha hb
  have h2 (q : Pattern) (ha : d139405 q = 1) (hb : d139697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d139405, d139697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139405, d139697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d139406 q = 1) (hb : d139698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d139406, d139698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139406, d139698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139407 q = 1) (hb : d139699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d139407, d139699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139407, d139699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d139408 q = 1) (hb : d139700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d139408, d139700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139408, d139700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139409 q = 1) (hb : d139701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d139409, d139701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139409, d139701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24694 (p : Pattern) (ha : d139415 p = 1) (hb : d139707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d139296 q = 1) (hb : d139536 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139296, d139536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24663 q ha hb
    | true =>
      simp only [d139296, d139536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24669 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d139323 q = 1) (hb : d139576 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139323, d139576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139323, d139576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24675 q ha hb
  have h3 (q : Pattern) (ha : d139324 q = 1) (hb : d139577 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139324, d139577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d139324, d139577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d139351 q = 1) (hb : d139617 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139351, d139617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139351, d139617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24681 q ha hb
  have h5 (q : Pattern) (ha : d139352 q = 1) (hb : d139618 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139352, d139618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139352, d139618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d139353 q = 1) (hb : d139619 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139353, d139619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139353, d139619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d139380 q = 1) (hb : d139659 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139380, d139659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139380, d139659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24687 q ha hb
  have h8 (q : Pattern) (ha : d139381 q = 1) (hb : d139660 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139381, d139660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139381, d139660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d139382 q = 1) (hb : d139661 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139382, d139661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139382, d139661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d139383 q = 1) (hb : d139662 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d139383, d139662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d139383, d139662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d139410 q = 1) (hb : d139702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d139410, d139702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139410, d139702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24693 q ha hb
  have h12 (q : Pattern) (ha : d139411 q = 1) (hb : d139703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d139411, d139703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139411, d139703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d139412 q = 1) (hb : d139704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d139412, d139704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139412, d139704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d139413 q = 1) (hb : d139705 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d139413, d139705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139413, d139705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d139414 q = 1) (hb : d139706 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d139414, d139706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d139414, d139706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d139415 q = 1) (hb : d139707 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d139415, d139707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d139415, d139707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro24695 (p : Pattern) (ha : d139421 p = 1) (hb : d139713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139416 q = 1) (hb : d139708 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d139416, d139708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24694 q ha hb
    | true =>
      simp only [d139416, d139708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139417 q = 1) (hb : d139709 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d139417, d139709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139417, d139709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139418 q = 1) (hb : d139710 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d139418, d139710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139418, d139710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139419 q = 1) (hb : d139711 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d139419, d139711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139419, d139711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139420 q = 1) (hb : d139712 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d139420, d139712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139420, d139712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139421 q = 1) (hb : d139713 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d139421, d139713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139421, d139713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24696 (p : Pattern) (ha : d139427 p = 1) (hb : d139719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139422 q = 1) (hb : d139714 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d139422, d139714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24695 q ha hb
    | true =>
      simp only [d139422, d139714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139423 q = 1) (hb : d139715 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d139423, d139715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139423, d139715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139424 q = 1) (hb : d139716 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d139424, d139716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139424, d139716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139425 q = 1) (hb : d139717 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d139425, d139717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139425, d139717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139426 q = 1) (hb : d139718 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d139426, d139718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139426, d139718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139427 q = 1) (hb : d139719 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d139427, d139719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139427, d139719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24697 (p : Pattern) (ha : d139433 p = 1) (hb : d139725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139428 q = 1) (hb : d139720 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d139428, d139720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24696 q ha hb
    | true =>
      simp only [d139428, d139720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139429 q = 1) (hb : d139721 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d139429, d139721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139429, d139721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139430 q = 1) (hb : d139722 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d139430, d139722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139430, d139722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139431 q = 1) (hb : d139723 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d139431, d139723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139431, d139723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139432 q = 1) (hb : d139724 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d139432, d139724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139432, d139724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139433 q = 1) (hb : d139725 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d139433, d139725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139433, d139725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24698 (p : Pattern) (ha : d139439 p = 1) (hb : d139731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139434 q = 1) (hb : d139726 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d139434, d139726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24697 q ha hb
    | true =>
      simp only [d139434, d139726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139435 q = 1) (hb : d139727 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d139435, d139727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139435, d139727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139436 q = 1) (hb : d139728 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d139436, d139728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139436, d139728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139437 q = 1) (hb : d139729 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d139437, d139729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139437, d139729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139438 q = 1) (hb : d139730 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d139438, d139730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139438, d139730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139439 q = 1) (hb : d139731 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d139439, d139731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139439, d139731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24699 (p : Pattern) (ha : d139445 p = 1) (hb : d139737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139440 q = 1) (hb : d139732 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d139440, d139732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24698 q ha hb
    | true =>
      simp only [d139440, d139732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139441 q = 1) (hb : d139733 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d139441, d139733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139441, d139733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139442 q = 1) (hb : d139734 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d139442, d139734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139442, d139734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139443 q = 1) (hb : d139735 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d139443, d139735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139443, d139735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139444 q = 1) (hb : d139736 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d139444, d139736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139444, d139736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139445 q = 1) (hb : d139737 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d139445, d139737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139445, d139737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24700 (p : Pattern) (ha : d139451 p = 1) (hb : d139743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139446 q = 1) (hb : d139738 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d139446, d139738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24699 q ha hb
    | true =>
      simp only [d139446, d139738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139447 q = 1) (hb : d139739 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d139447, d139739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139447, d139739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139448 q = 1) (hb : d139740 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d139448, d139740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139448, d139740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139449 q = 1) (hb : d139741 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d139449, d139741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139449, d139741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139450 q = 1) (hb : d139742 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d139450, d139742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139450, d139742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139451 q = 1) (hb : d139743 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d139451, d139743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139451, d139743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24701 (p : Pattern) (ha : d139457 p = 1) (hb : d139749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139452 q = 1) (hb : d139744 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d139452, d139744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24700 q ha hb
    | true =>
      simp only [d139452, d139744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d139453 q = 1) (hb : d139745 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d139453, d139745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d139453, d139745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d139454 q = 1) (hb : d139746 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d139454, d139746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d139454, d139746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d139455 q = 1) (hb : d139747 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d139455, d139747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d139455, d139747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139456 q = 1) (hb : d139748 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d139456, d139748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d139456, d139748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d139457 q = 1) (hb : d139749 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d139457, d139749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d139457, d139749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24702 (p : Pattern) (ha : d74831 p = 1) (hb : d115573 p = 1) : d85701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d77842 q = 1) : d85696 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14594 q ha hb
    | true =>
      simp only [d74826, d85696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d77842 q = 1) : d85697 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d85697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74828 q = 1) (hb : d115571 q = 1) : d85698 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d115571, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d115571, d85698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115571 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74829 q = 1) (hb : d115571 q = 1) : d85699 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74829, d85699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115572 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d74830 q = 1) (hb : d115573 q = 1) : d85700 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d115573, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74830, d115573, d85700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d74831 q = 1) (hb : d115573 q = 1) : d85701 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74831, d85701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24703 (p : Pattern) (ha : d74837 p = 1) (hb : d115573 p = 1) : d85707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d115573 q = 1) : d85702 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24702 q ha hb
    | true =>
      simp only [d74832, d85702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d115573 q = 1) : d85703 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d85703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d115573 q = 1) : d85704 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d85704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d115573 q = 1) : d85705 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d85705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d115573 q = 1) : d85706 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d85706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d115573 q = 1) : d85707 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d85707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24704 (p : Pattern) (ha : d74843 p = 1) (hb : d115573 p = 1) : d85713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d115573 q = 1) : d85708 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24703 q ha hb
    | true =>
      simp only [d74838, d85708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d115573 q = 1) : d85709 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d85709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d115573 q = 1) : d85710 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d85710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d115573 q = 1) : d85711 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d85711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d115573 q = 1) : d85712 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d85712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d115573 q = 1) : d85713 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d85713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24705 (p : Pattern) (ha : d74849 p = 1) (hb : d115573 p = 1) : d85719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d115573 q = 1) : d85714 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24704 q ha hb
    | true =>
      simp only [d74844, d85714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d115573 q = 1) : d85715 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d85715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d115573 q = 1) : d85716 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d85716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d115573 q = 1) : d85717 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d85717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d115573 q = 1) : d85718 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d85718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d115573 q = 1) : d85719 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d85719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24706 (p : Pattern) (ha : d53847 p = 1) (hb : d115573 p = 1) : d99391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d77842 q = 1) : d99386 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14688 q ha hb
    | true =>
      simp only [d53842, d99386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d77842 q = 1) : d99387 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d99387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53844 q = 1) (hb : d115571 q = 1) : d99388 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d115571, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d115571, d99388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115571 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53845 q = 1) (hb : d115571 q = 1) : d99389 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53845, d99389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115572 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53846 q = 1) (hb : d115573 q = 1) : d99390 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d115573, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53846, d115573, d99390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53847 q = 1) (hb : d115573 q = 1) : d99391 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53847, d99391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24707 (p : Pattern) (ha : d53853 p = 1) (hb : d115573 p = 1) : d99397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d115573 q = 1) : d99392 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24706 q ha hb
    | true =>
      simp only [d53848, d99392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d115573 q = 1) : d99393 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d99393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d115573 q = 1) : d99394 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d99394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d115573 q = 1) : d99395 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d99395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d115573 q = 1) : d99396 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d99396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d115573 q = 1) : d99397 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d99397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24708 (p : Pattern) (ha : d53859 p = 1) (hb : d115573 p = 1) : d99403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d115573 q = 1) : d99398 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24707 q ha hb
    | true =>
      simp only [d53854, d99398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d115573 q = 1) : d99399 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d99399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d115573 q = 1) : d99400 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d99400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d115573 q = 1) : d99401 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d99401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d115573 q = 1) : d99402 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d99402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d115573 q = 1) : d99403 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d99403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24709 (p : Pattern) (ha : d53865 p = 1) (hb : d115573 p = 1) : d99409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d115573 q = 1) : d99404 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24708 q ha hb
    | true =>
      simp only [d53860, d99404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d115573 q = 1) : d99405 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d99405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d115573 q = 1) : d99406 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d99406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d115573 q = 1) : d99407 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d99407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d115573 q = 1) : d99408 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d99408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d115573 q = 1) : d99409 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d99409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24710 (p : Pattern) (ha : d74849 p = 1) (hb : d139752 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d139752 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24711 (p : Pattern) (ha : d53865 p = 1) (hb : d139752 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d139752 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro24712 (p : Pattern) (ha : d10654 p = 1) (hb : d107483 p = 1) : d110577 p = 1 := by
  have h0 (q : Pattern) (ha : d10652 q = 1) (hb : d85721 q = 1) : d10652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10653 q = 1) (hb : d107483 q = 1) : d110576 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d107483, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10653, d107483, d110576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10654 q = 1) (hb : d107483 q = 1) : d110577 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10654, d110577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24713 (p : Pattern) (ha : d10660 p = 1) (hb : d107483 p = 1) : d110583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d107483 q = 1) : d110582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10660 q = 1) (hb : d107483 q = 1) : d110583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d110583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24714 (p : Pattern) (ha : d107483 p = 1) (hb : d108784 p = 1) : d110589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d107483 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d107483 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10661 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
    | true =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108780 q = 1) : d110585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108780, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d107483 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108781 q = 1) : d110586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108782 q = 1) : d110587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108782, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108783 q = 1) : d110588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108783, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108784 q = 1) : d110589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108784, d110589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro24715 (p : Pattern) (ha : d10667 p = 1) (hb : d107483 p = 1) : d110590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d107483 q = 1) : d110582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d110582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10667 q = 1) (hb : d107483 q = 1) : d110590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10667, d110590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24716 (p : Pattern) (ha : d107483 p = 1) (hb : d108789 p = 1) : d110596 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d107483 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d107483 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10661 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
    | true =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108780 q = 1) : d110585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108780, d110585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d107483 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108781 q = 1) : d110586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d110586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108782 q = 1) : d110587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108782, d110587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108783 q = 1) : d110588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108783, d110588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d107483 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d107483 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10668 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
    | true =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108785 q = 1) : d110592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d108785, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d107483 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108786 q = 1) : d110593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108786, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108787 q = 1) : d110594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d108787, d110594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d108788 q = 1) : d110595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108788, d110595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d107483 q = 1) (hb : d108789 q = 1) : d110596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108789, d110596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro24717 (p : Pattern) (ha : d107483 p = 1) (hb : d108796 p = 1) : d110603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
    | true =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108785 q = 1) : d110592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108785, d110592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d107483 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108786 q = 1) : d110593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108786, d110593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108794 q = 1) : d110601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108794, d110601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108795 q = 1) : d110602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108795, d110602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108796 q = 1) : d110603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108796, d110603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24718 (p : Pattern) (ha : d10691 p = 1) (hb : d107483 p = 1) : d110610 p = 1 := by
  have h0 (q : Pattern) (ha : d10689 q = 1) (hb : d85721 q = 1) : d10689 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10690 q = 1) (hb : d107483 q = 1) : d110609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d107483, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10690, d107483, d110609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10691 q = 1) (hb : d107483 q = 1) : d110610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10691, d110610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24719 (p : Pattern) (ha : d10697 p = 1) (hb : d107483 p = 1) : d110616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24718 q ha hb
    | true =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d107483 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10694 q = 1) (hb : d107483 q = 1) : d110613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d110613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10695 q = 1) (hb : d107483 q = 1) : d110614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10695, d110614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10696 q = 1) (hb : d107483 q = 1) : d110615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10696, d110615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10697 q = 1) (hb : d107483 q = 1) : d110616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10697, d110616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24720 (p : Pattern) (ha : d107483 p = 1) (hb : d108806 p = 1) : d110622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d107483 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d107483 q = 1) : d110617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24719 q ha hb
    | true =>
      simp only [d10698, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108802 q = 1) : d110618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d108802, d110618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d107483 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108803 q = 1) : d110619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108803, d110619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108804 q = 1) : d110620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108804, d110620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108805 q = 1) : d110621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108805, d110621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108806 q = 1) : d110622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108806, d110622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24721 (p : Pattern) (ha : d107483 p = 1) (hb : d108812 p = 1) : d110628 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d107483 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d108790 q = 1) : d110597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24714 q ha hb
    | true =>
      simp only [d108790, d110597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24716 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d107483 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108791 q = 1) : d110598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108791, d110598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108792 q = 1) : d110599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108792, d110599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108793 q = 1) : d110600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108793, d110600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108797 q = 1) : d110604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108797, d110604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24717 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108798 q = 1) : d110605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108798, d110605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108799 q = 1) : d110606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108799, d110606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108800 q = 1) : d110607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108800, d110607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108801 q = 1) : d110608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108801, d110608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108807 q = 1) : d110623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108807, d110623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24720 q ha hb
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d108808 q = 1) : d110624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108808, d110624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108809 q = 1) : d110625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108809, d110625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108810 q = 1) : d110626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108810, d110626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108811 q = 1) : d110627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108811, d110627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108812 q = 1) : d110628 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108812, d110628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24722 (p : Pattern) (ha : d10719 p = 1) (hb : d107483 p = 1) : d110638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
    | true =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10719 q = 1) (hb : d107483 q = 1) : d110638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24723 (p : Pattern) (ha : d10726 p = 1) (hb : d107483 p = 1) : d110645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
    | true =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10668 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
    | true =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10722 q = 1) (hb : d107483 q = 1) : d110641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10723 q = 1) (hb : d107483 q = 1) : d110642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10723, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10724 q = 1) (hb : d107483 q = 1) : d110643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10725 q = 1) (hb : d107483 q = 1) : d110644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10726 q = 1) (hb : d107483 q = 1) : d110645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10726, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24724 (p : Pattern) (ha : d10801 p = 1) (hb : d107483 p = 1) : d110701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d107483 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d107483 q = 1) : d110584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
    | true =>
      simp only [d10661, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d107483 q = 1) : d110634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d107483 q = 1) : d110635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d107483 q = 1) : d110636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d107483 q = 1) : d110637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d107483 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10801 q = 1) (hb : d107483 q = 1) : d110701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10801, d110701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24725 (p : Pattern) (ha : d10731 p = 1) (hb : d107483 p = 1) : d110650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d107483 q = 1) : d110649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10731 q = 1) (hb : d107483 q = 1) : d110650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d110650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24726 (p : Pattern) (ha : d10738 p = 1) (hb : d107483 p = 1) : d110657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d107483 q = 1) : d110655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d107483 q = 1) : d110656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10738 q = 1) (hb : d107483 q = 1) : d110657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d110657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24727 (p : Pattern) (ha : d10747 p = 1) (hb : d107483 p = 1) : d110662 p = 1 := by
  have h0 (q : Pattern) (ha : d10745 q = 1) (hb : d85721 q = 1) : d10745 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10746 q = 1) (hb : d107483 q = 1) : d110661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10746, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10747 q = 1) (hb : d107483 q = 1) : d110662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10747, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24728 (p : Pattern) (ha : d10753 p = 1) (hb : d107483 p = 1) : d110668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24727 q ha hb
    | true =>
      simp only [d10748, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d107483 q = 1) : d110665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d107483 q = 1) : d110666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d107483 q = 1) : d110667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d107483 q = 1) : d110668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d110668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24729 (p : Pattern) (ha : d10772 p = 1) (hb : d107483 p = 1) : d110674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d107483 q = 1) : d110671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d107483 q = 1) : d110672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d107483 q = 1) : d110673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d107483 q = 1) : d110674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d110674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro24730 (p : Pattern) (ha : d107483 p = 1) (hb : d108822 p = 1) : d110680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d107483 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d107483 q = 1) : d110651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24725 q ha hb
    | true =>
      simp only [d10732, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d107483 q = 1) : d110652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d107483 q = 1) : d110653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d107483 q = 1) : d110654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d107483 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d107483 q = 1) : d110658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24726 q ha hb
    | true =>
      simp only [d10739, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d107483 q = 1) : d110659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d107483 q = 1) : d110660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d107483 q = 1) : d110669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24728 q ha hb
    | true =>
      simp only [d10754, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108818 q = 1) : d110670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108818, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d107483 q = 1) : d110675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24729 q ha hb
    | true =>
      simp only [d10773, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d107483 q = 1) : d110676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108819 q = 1) : d110677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108820 q = 1) : d110678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108820, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108821 q = 1) : d110679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108821, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108822 q = 1) : d110680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108822, d110680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro24731 (p : Pattern) (ha : d10779 p = 1) (hb : d107483 p = 1) : d110681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d107483 q = 1) : d110581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d110581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d107483 q = 1) : d110649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d110649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10779 q = 1) (hb : d107483 q = 1) : d110681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10779, d110681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24732 (p : Pattern) (ha : d10784 p = 1) (hb : d107483 p = 1) : d110686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d107483 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d107483 q = 1) : d110580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d110580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d107483 q = 1) : d110655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d110655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d107483 q = 1) : d110656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d110656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10784 q = 1) (hb : d107483 q = 1) : d110686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10784, d110686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24733 (p : Pattern) (ha : d10788 p = 1) (hb : d107483 p = 1) : d110690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24727 q ha hb
    | true =>
      simp only [d10748, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d107483 q = 1) : d110665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d110665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d107483 q = 1) : d110666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d110666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d107483 q = 1) : d110667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d110667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d107483 q = 1) : d110690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d110690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24734 (p : Pattern) (ha : d10793 p = 1) (hb : d107483 p = 1) : d110693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107483 q = 1) : d110578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24712 q ha hb
    | true =>
      simp only [d10655, d110578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107483 q = 1) : d110579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d110579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d107483 q = 1) : d110671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d110671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d107483 q = 1) : d110672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d110672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d107483 q = 1) : d110673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d110673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d107483 q = 1) : d110693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d110693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24735 (p : Pattern) (ha : d107483 p = 1) (hb : d108827 p = 1) : d110699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d107483 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d107483 q = 1) : d110651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24725 q ha hb
    | true =>
      simp only [d10732, d110651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d107483 q = 1) : d110652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d110652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d107483 q = 1) : d110653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d110653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d107483 q = 1) : d110654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d110654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d107483 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d107483 q = 1) : d110658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24726 q ha hb
    | true =>
      simp only [d10739, d110658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d107483 q = 1) : d110659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d110659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d107483 q = 1) : d110660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d110660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d107483 q = 1) : d110669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24728 q ha hb
    | true =>
      simp only [d10754, d110669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24713 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108818 q = 1) : d110670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d108818, d110670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d107483 q = 1) : d110675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24729 q ha hb
    | true =>
      simp only [d10773, d110675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d107483 q = 1) : d110676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d110676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108819 q = 1) : d110677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d110677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108820 q = 1) : d110678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d108820, d110678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108821 q = 1) : d110679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108821, d110679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d107483 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10780 q = 1) (hb : d107483 q = 1) : d110682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24731 q ha hb
    | true =>
      simp only [d10780, d110682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10781 q = 1) (hb : d107483 q = 1) : d110683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d110683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10782 q = 1) (hb : d107483 q = 1) : d110684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10782, d110684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10783 q = 1) (hb : d107483 q = 1) : d110685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d110685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d107483 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10785 q = 1) (hb : d107483 q = 1) : d110687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24732 q ha hb
    | true =>
      simp only [d10785, d110687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10786 q = 1) (hb : d107483 q = 1) : d110688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d110688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10787 q = 1) (hb : d107483 q = 1) : d110689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10787, d110689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10789 q = 1) (hb : d107483 q = 1) : d110691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24733 q ha hb
    | true =>
      simp only [d10789, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
  have h27 (q : Pattern) (ha : d107483 q = 1) (hb : d108823 q = 1) : d110692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d108823, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d10794 q = 1) (hb : d107483 q = 1) : d110694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24734 q ha hb
    | true =>
      simp only [d10794, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10795 q = 1) (hb : d107483 q = 1) : d110695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10795, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d107483 q = 1) (hb : d108824 q = 1) : d110696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108824, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d107483 q = 1) (hb : d108825 q = 1) : d110697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d108825, d110697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d107483 q = 1) (hb : d108826 q = 1) : d110698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108826, d110698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d107483 q = 1) (hb : d108827 q = 1) : d110699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108827, d110699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro24736 (p : Pattern) (ha : d107483 p = 1) (hb : d108834 p = 1) : d110708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d107483 q = 1) : d110691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24733 q ha hb
    | true =>
      simp only [d10789, d110691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108823 q = 1) : d110692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d110692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d107483 q = 1) : d110694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24734 q ha hb
    | true =>
      simp only [d10794, d110694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d107483 q = 1) : d110695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d110695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108824 q = 1) : d110696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d110696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108832 q = 1) : d110706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108832, d110706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108833 q = 1) : d110707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108833, d110707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108834 q = 1) : d110708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108834, d110708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24737 (p : Pattern) (ha : d10819 p = 1) (hb : d107483 p = 1) : d110715 p = 1 := by
  have h0 (q : Pattern) (ha : d10817 q = 1) (hb : d85721 q = 1) : d10817 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10818 q = 1) (hb : d107483 q = 1) : d110714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10818, d107483, d110714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10819 q = 1) (hb : d107483 q = 1) : d110715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10819, d110715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24738 (p : Pattern) (ha : d10825 p = 1) (hb : d107483 p = 1) : d110721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d107483 q = 1) : d110716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24737 q ha hb
    | true =>
      simp only [d10820, d110716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d107483 q = 1) : d110717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d110717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24718 q ha hb
    | true =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d107483 q = 1) : d110718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d110718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d107483 q = 1) : d110719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d110719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d107483 q = 1) : d110720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d110720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d107483 q = 1) : d110721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d110721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro24739 (p : Pattern) (ha : d10844 p = 1) (hb : d107483 p = 1) : d110727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d107483 q = 1) : d110611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24718 q ha hb
    | true =>
      simp only [d10692, d110611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d107483 q = 1) : d110612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d110612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d107483 q = 1) : d110724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d110724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d107483 q = 1) : d110725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d110725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d107483 q = 1) : d110726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d110726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d107483 q = 1) : d110727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d110727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro24740 (p : Pattern) (ha : d107483 p = 1) (hb : d108844 p = 1) : d110733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d107483 q = 1) : d110722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24738 q ha hb
    | true =>
      simp only [d10826, d110722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24719 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108840 q = 1) : d110723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d110723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d107483 q = 1) : d110728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24739 q ha hb
    | true =>
      simp only [d10845, d110728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d107483 q = 1) : d110729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d110729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108841 q = 1) : d110730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d110730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108842 q = 1) : d110731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108842, d110731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108843 q = 1) : d110732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108843, d110732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108844 q = 1) : d110733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108844, d110733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24741 (p : Pattern) (ha : d107483 p = 1) (hb : d108850 p = 1) : d110739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d107483 q = 1) : d110639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d110639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24722 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d107483 q = 1) : d110640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d110640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d107483 q = 1) : d110646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24722 q ha hb
    | true =>
      simp only [d10727, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24723 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d107483 q = 1) : d110647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d107483 q = 1) : d110648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d110648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108828 q = 1) : d110700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24730 q ha hb
    | true =>
      simp only [d108828, d110700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24735 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d107483 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10802 q = 1) (hb : d107483 q = 1) : d110702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24724 q ha hb
    | true =>
      simp only [d10802, d110702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108829 q = 1) : d110703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d110703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108830 q = 1) : d110704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108830, d110704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108831 q = 1) : d110705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108831, d110705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108835 q = 1) : d110709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108835, d110709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24736 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d107483 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d108836 q = 1) : d110710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108836, d110710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d108837 q = 1) : d110711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108837, d110711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d108838 q = 1) : d110712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108838, d110712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d107483 q = 1) (hb : d108839 q = 1) : d110713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108839, d110713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107483 q = 1) (hb : d108845 q = 1) : d110734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108845, d110734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24740 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d107483 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d107483 q = 1) (hb : d108846 q = 1) : d110735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108846, d110735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d107483 q = 1) (hb : d108847 q = 1) : d110736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108847, d110736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107483 q = 1) (hb : d108848 q = 1) : d110737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108848, d110737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107483 q = 1) (hb : d108849 q = 1) : d110738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108849, d110738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d107483 q = 1) (hb : d108850 q = 1) : d110739 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108850, d110739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro24742 (p : Pattern) (ha : d107483 p = 1) (hb : d108856 p = 1) : d110745 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d107483 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d108813 q = 1) : d110629 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108813, d110629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24721 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d108814 q = 1) : d110630 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108814, d110630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d108815 q = 1) : d110631 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108815, d110631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d108816 q = 1) : d110632 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108816, d110632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d108817 q = 1) : d110633 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108817, d110633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d108851 q = 1) : d110740 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108851, d110740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24741 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d108852 q = 1) : d110741 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108852, d110741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d108853 q = 1) : d110742 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108853, d110742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d108854 q = 1) : d110743 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108854, d110743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d108855 q = 1) : d110744 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108855, d110744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d108856 q = 1) : d110745 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108856, d110745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro24743 (p : Pattern) (ha : d10865 p = 1) (hb : d107483 p = 1) : d110662 p = 1 := by
  have h0 (q : Pattern) (ha : d10745 q = 1) (hb : d85721 q = 1) : d10745 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10863 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10864 q = 1) (hb : d107483 q = 1) : d110661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10864, d107483, d110661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10865 q = 1) (hb : d107483 q = 1) : d110662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10865, d110662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro24744 (p : Pattern) (ha : d10875 p = 1) (hb : d107483 p = 1) : d110749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10874 q = 1) (hb : d107483 q = 1) : d110748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10874, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10875 q = 1) (hb : d107483 q = 1) : d110749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d110749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24745 (p : Pattern) (ha : d10885 p = 1) (hb : d107483 p = 1) : d110755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d107483 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24744 q ha hb
    | true =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10885 q = 1) (hb : d107483 q = 1) : d110755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro24746 (p : Pattern) (ha : d10888 p = 1) (hb : d107483 p = 1) : d110758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10874 q = 1) (hb : d107483 q = 1) : d110748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10874, d110748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10888 q = 1) (hb : d107483 q = 1) : d110758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10888, d110758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro24747 (p : Pattern) (ha : d10895 p = 1) (hb : d107483 p = 1) : d110764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d107483 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24744 q ha hb
    | true =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10889 q = 1) (hb : d107483 q = 1) : d10889 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10890 q = 1) (hb : d107483 q = 1) : d110759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24746 q ha hb
    | true =>
      simp only [d10890, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10891 q = 1) (hb : d107483 q = 1) : d110760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10892 q = 1) (hb : d107483 q = 1) : d110761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10892, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10893 q = 1) (hb : d107483 q = 1) : d110762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10894 q = 1) (hb : d107483 q = 1) : d110763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10895 q = 1) (hb : d107483 q = 1) : d110764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10895, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro24748 (p : Pattern) (ha : d10992 p = 1) (hb : d107483 p = 1) : d110820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d107483 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d107483 q = 1) : d110750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24744 q ha hb
    | true =>
      simp only [d10880, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d107483 q = 1) : d110751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d107483 q = 1) : d110752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d107483 q = 1) : d110753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d107483 q = 1) : d110754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10991 q = 1) (hb : d107483 q = 1) : d10991 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10992 q = 1) (hb : d107483 q = 1) : d110820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10992, d110820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro24749 (p : Pattern) (ha : d10900 p = 1) (hb : d107483 p = 1) : d110769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107483 q = 1) : d110663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24743 q ha hb
    | true =>
      simp only [d10866, d110663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107483 q = 1) : d110664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d110664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d107483 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d107483 q = 1) : d110746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d110746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d107483 q = 1) : d110747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d110747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10899 q = 1) (hb : d107483 q = 1) : d110768 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d110768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10900 q = 1) (hb : d107483 q = 1) : d110769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d110769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
