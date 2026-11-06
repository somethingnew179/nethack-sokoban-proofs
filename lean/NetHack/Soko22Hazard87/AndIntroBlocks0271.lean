import NetHack.Soko22Hazard87.AndIntroBlocks0270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro67750 (p : Pattern) (ha : d27812 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27580 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67717 q ha hb
    | true =>
      simp only [d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27581 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27584 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67718 q ha hb
    | true =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27585 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27586 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27587 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27613 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27812 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67751 (p : Pattern) (ha : d27813 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27584 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67718 q ha hb
    | true =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27585 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27590 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27591 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27615 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27813 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67752 (p : Pattern) (ha : d27818 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27580 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67717 q ha hb
    | true =>
      simp only [d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27581 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27584 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67718 q ha hb
    | true =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27585 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27586 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27621 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27622 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27818 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67753 (p : Pattern) (ha : d27819 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27584 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67718 q ha hb
    | true =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27585 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27590 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27624 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27625 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27819 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67754 (p : Pattern) (ha : d27823 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27662 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67744 q ha hb
    | true =>
      simp only [d27662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27663 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27667 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67725 q ha hb
    | true =>
      simp only [d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27668 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27669 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27670 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27671 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27823 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67755 (p : Pattern) (ha : d27824 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27667 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67725 q ha hb
    | true =>
      simp only [d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27668 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27584 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67718 q ha hb
    | true =>
      simp only [d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27585 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27673 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27674 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27675 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27824 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67756 (p : Pattern) (ha : d27830 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27800 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67747 q ha hb
    | true =>
      simp only [d27800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27801 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27802 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27803 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27804 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27830 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67757 (p : Pattern) (ha : d171300 p = 1) (hb : d212318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27617 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67735 q ha hb
    | true =>
      simp only [d27617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67736 q ha hb
  have h2 (q : Pattern) (ha : d27618 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27619 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27620 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27627 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67737 q ha hb
    | true =>
      simp only [d27627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67738 q ha hb
  have h6 (q : Pattern) (ha : d27628 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27629 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27677 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67745 q ha hb
    | true =>
      simp only [d27677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67726 q ha hb
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d212309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d27806 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67748 q ha hb
    | true =>
      simp only [d27806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27807 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212310 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212311 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212312 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27814 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67750 q ha hb
    | true =>
      simp only [d27814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67751 q ha hb
  have h16 (q : Pattern) (ha : d27815 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27816 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d27817 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d27820 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67752 q ha hb
    | true =>
      simp only [d27820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67753 q ha hb
  have h20 (q : Pattern) (ha : d27821 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d27822 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d27822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d27825 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67754 q ha hb
    | true =>
      simp only [d27825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67755 q ha hb
  have h23 (q : Pattern) (ha : d171300 q = 1) (hb : d212314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d27831 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67756 q ha hb
    | true =>
      simp only [d27831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d27832 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d27832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d171300 q = 1) (hb : d212315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d171300 q = 1) (hb : d212316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d212316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d171300 q = 1) (hb : d212317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d212317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d171300 q = 1) (hb : d212318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d212318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro67758 (p : Pattern) (ha : d171300 p = 1) (hb : d212325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27825 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67754 q ha hb
    | true =>
      simp only [d27825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67755 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d27831 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67756 q ha hb
    | true =>
      simp only [d27831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27832 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67759 (p : Pattern) (ha : d27883 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27869 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67739 q ha hb
  have h2 (q : Pattern) (ha : d27631 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67739 q ha hb
    | true =>
      simp only [d27631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27870 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27632 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27871 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27872 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27872, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27872, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27873 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67740 q ha hb
  have h9 (q : Pattern) (ha : d27636 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67740 q ha hb
    | true =>
      simp only [d27636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27874 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27637 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27875 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27876 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27876, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27876, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d27877 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15380 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38436 q ha hb
  have h16 (q : Pattern) (ha : d10046 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38436 q ha hb
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d15381 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10048 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d15382 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d15382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15383 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15383, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h21 (q : Pattern) (ha : d27878 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67706 q ha hb
  have h22 (q : Pattern) (ha : d27504 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67706 q ha hb
    | true =>
      simp only [d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d27879 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d27879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d27505 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d27880 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d27880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d27881 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27881, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d27881, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h27 (q : Pattern) (ha : d27882 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d27882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d27883 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro67760 (p : Pattern) (ha : d27898 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27884 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67704 q ha hb
  have h2 (q : Pattern) (ha : d27490 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67704 q ha hb
    | true =>
      simp only [d27490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27885 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27491 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27886 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27887 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27887, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27887, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27888 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67705 q ha hb
  have h9 (q : Pattern) (ha : d27495 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67705 q ha hb
    | true =>
      simp only [d27495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27889 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27496 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27890 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27891 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27891, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27891, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d27892 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27878 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67706 q ha hb
  have h16 (q : Pattern) (ha : d27504 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67706 q ha hb
    | true =>
      simp only [d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d27879 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d27879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d27505 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d27880 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d27880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d27881 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27881, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d27881, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h21 (q : Pattern) (ha : d27893 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67707 q ha hb
  have h22 (q : Pattern) (ha : d27512 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67707 q ha hb
    | true =>
      simp only [d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d27894 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d27513 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d27895 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d27896 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27896, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d27896, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h27 (q : Pattern) (ha : d27897 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d27897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d27898 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro67761 (p : Pattern) (ha : d27908 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27902 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67742 q ha hb
  have h2 (q : Pattern) (ha : d27650 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67742 q ha hb
    | true =>
      simp only [d27650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27903 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27651 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27904 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27905 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27905, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27905, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27893 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67707 q ha hb
  have h9 (q : Pattern) (ha : d27512 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67707 q ha hb
    | true =>
      simp only [d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27894 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27513 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27895 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27896 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27896, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27896, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d27906 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d27907 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27908 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67762 (p : Pattern) (ha : d27936 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27926 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67712 q ha hb
  have h2 (q : Pattern) (ha : d27542 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67712 q ha hb
    | true =>
      simp only [d27542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27927 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27543 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27928 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27929 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27929, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27929, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d27930 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27931 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67713 q ha hb
  have h11 (q : Pattern) (ha : d27554 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67713 q ha hb
    | true =>
      simp only [d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27932 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27555 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d27933 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27934 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27934, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27934, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h16 (q : Pattern) (ha : d27935 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d27935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h17 (q : Pattern) (ha : d27936 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67763 (p : Pattern) (ha : d27942 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27899 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67759 q ha hb
    | true =>
      simp only [d27899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
  have h2 (q : Pattern) (ha : d27900 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27901 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27909 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
    | true =>
      simp only [d27909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67761 q ha hb
  have h5 (q : Pattern) (ha : d27910 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27911 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27912 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27923 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
    | true =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
  have h9 (q : Pattern) (ha : d27924 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27925 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27937 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67762 q ha hb
  have h12 (q : Pattern) (ha : d27938 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27939 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27940 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27941 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27942 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d27942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro67764 (p : Pattern) (ha : d27947 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
    | true =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67762 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27945 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27946 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27947 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro67765 (p : Pattern) (ha : d27953 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27943 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67763 q ha hb
    | true =>
      simp only [d27943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27944 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27948 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67764 q ha hb
    | true =>
      simp only [d27948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27949 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27950 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27951 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27952 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27953 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67766 (p : Pattern) (ha : d27971 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27948 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67764 q ha hb
    | true =>
      simp only [d27948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27949 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27966 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67732 q ha hb
    | true =>
      simp only [d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27967 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27968 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27969 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27970 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27971 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67767 (p : Pattern) (ha : d28049 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27954 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67715 q ha hb
  have h2 (q : Pattern) (ha : d27568 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67715 q ha hb
    | true =>
      simp only [d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27955 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27569 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27956 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27957 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27957, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27957, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d27958 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28049 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro67768 (p : Pattern) (ha : d28055 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
    | true =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67762 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28050 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d28050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67767 q ha hb
  have h9 (q : Pattern) (ha : d28051 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28052 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28053 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28054 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28055 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro67769 (p : Pattern) (ha : d28061 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28056 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67768 q ha hb
    | true =>
      simp only [d28056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28057 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28058 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28059 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28060 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28061 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67770 (p : Pattern) (ha : d171300 p = 1) (hb : d212335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27972 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67765 q ha hb
    | true =>
      simp only [d27972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67766 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d28062 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67769 q ha hb
    | true =>
      simp only [d28062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28063 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67771 (p : Pattern) (ha : d171300 p = 1) (hb : d212341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27600 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67721 q ha hb
  have h2 (q : Pattern) (ha : d27601 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27610 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67721 q ha hb
    | true =>
      simp only [d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67724 q ha hb
  have h4 (q : Pattern) (ha : d27611 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27612 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d27612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67749 q ha hb
    | true =>
      simp only [d212319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67757 q ha hb
  have h7 (q : Pattern) (ha : d27855 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67727 q ha hb
    | true =>
      simp only [d27855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67728 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212321 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d212321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212322 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d212322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67758 q ha hb
  have h12 (q : Pattern) (ha : d27864 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67729 q ha hb
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212327 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212328 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212329 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d212329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d171300 q = 1) (hb : d212330 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d171300 q = 1) (hb : d212336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67770 q ha hb
  have h18 (q : Pattern) (ha : d28079 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67734 q ha hb
  have h19 (q : Pattern) (ha : d171300 q = 1) (hb : d212337 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d171300 q = 1) (hb : d212338 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d212338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d171300 q = 1) (hb : d212339 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d212339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d171300 q = 1) (hb : d212340 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d212340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d171300 q = 1) (hb : d212341 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67772 (p : Pattern) (ha : d171300 p = 1) (hb : d212347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212342 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67771 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212343 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212344 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212345 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212346 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212347 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67773 (p : Pattern) (ha : d28103 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28098 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28101 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28102 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28103 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67774 (p : Pattern) (ha : d28108 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28101 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28102 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28108 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro67775 (p : Pattern) (ha : d28117 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28116 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28116, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28116, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28117 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro67776 (p : Pattern) (ha : d28125 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28124 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28124, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28124, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5244 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5245 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28125 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67777 (p : Pattern) (ha : d28131 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28104 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67773 q ha hb
    | true =>
      simp only [d28104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28105 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28106 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28107 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28107, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28107, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28109 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67774 q ha hb
    | true =>
      simp only [d28109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28110 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28111 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28112 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28112, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28112, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d28113 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28120 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28121 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d28128 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28129 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d28130 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d28131 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro67778 (p : Pattern) (ha : d28136 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28101 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28102 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28102, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28135 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28136 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67779 (p : Pattern) (ha : d28141 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28135 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5244 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5245 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28141 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67780 (p : Pattern) (ha : d28148 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28137 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67778 q ha hb
    | true =>
      simp only [d28137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28138 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28139 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28140 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28140, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28140, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28142 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67779 q ha hb
    | true =>
      simp only [d28142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28143 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28144 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28145 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28145, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28145, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d28146 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28128 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28129 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d28147 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28148 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67781 (p : Pattern) (ha : d28155 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28153 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28154 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28154, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28154, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5244 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5245 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d5245, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28155 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67782 (p : Pattern) (ha : d28167 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28165 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28166 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28166, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28166, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28167 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro67783 (p : Pattern) (ha : d28173 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28156 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67781 q ha hb
    | true =>
      simp only [d28156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28157 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28158 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28159 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28159, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28159, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28160 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28168 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
    | true =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28169 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28170 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28171 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28171, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28171, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d28172 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d28173 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67784 (p : Pattern) (ha : d28181 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28135 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28135, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28179 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28180 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28180, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d28180, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d28181 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro67785 (p : Pattern) (ha : d28187 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28182 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
    | true =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28183 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28184 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28185 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28185, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28185, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28186 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28168 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
    | true =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28169 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28170 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28171 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28171, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28171, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d28172 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d28187 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67786 (p : Pattern) (ha : d28193 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28149 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
    | true =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
  have h2 (q : Pattern) (ha : d28150 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28151 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28174 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67783 q ha hb
  have h5 (q : Pattern) (ha : d28175 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28176 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28177 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28188 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67785 q ha hb
  have h9 (q : Pattern) (ha : d28189 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28190 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28191 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28192 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28193 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro67787 (p : Pattern) (ha : d28197 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28188 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67785 q ha hb
  have h2 (q : Pattern) (ha : d28189 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28190 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28191 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28196 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28197 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67788 (p : Pattern) (ha : d28203 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28201 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28202 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28203 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67789 (p : Pattern) (ha : d28207 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28205 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28206 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28207 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67790 (p : Pattern) (ha : d28213 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28208 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67788 q ha hb
    | true =>
      simp only [d28208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67789 q ha hb
  have h2 (q : Pattern) (ha : d28209 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28210 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28211 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28212 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28213 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67791 (p : Pattern) (ha : d28216 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28201 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28202 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28216 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67792 (p : Pattern) (ha : d28217 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28205 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28206 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28217 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67793 (p : Pattern) (ha : d28223 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28208 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67788 q ha hb
    | true =>
      simp only [d28208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67789 q ha hb
  have h2 (q : Pattern) (ha : d28209 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28210 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28211 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28212 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28218 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67791 q ha hb
    | true =>
      simp only [d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67792 q ha hb
  have h7 (q : Pattern) (ha : d28219 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28220 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28221 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28222 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28223 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67794 (p : Pattern) (ha : d28271 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28149 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
    | true =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
  have h2 (q : Pattern) (ha : d28150 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28151 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28174 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67783 q ha hb
  have h5 (q : Pattern) (ha : d28175 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28176 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28177 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28269 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28270 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28271 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro67795 (p : Pattern) (ha : d28281 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28272 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67794 q ha hb
    | true =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28273 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28278 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28279 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28280 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28281 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67796 (p : Pattern) (ha : d28453 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28443 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67795 q ha hb
    | true =>
      simp only [d28443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67789 q ha hb
  have h2 (q : Pattern) (ha : d28444 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28445 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28446 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28447 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28448 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67789 q ha hb
    | true =>
      simp only [d28448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28449 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28450 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28451 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28452 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28453 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67797 (p : Pattern) (ha : d28459 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28448 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67789 q ha hb
    | true =>
      simp only [d28448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28449 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28450 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28451 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28452 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28454 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67792 q ha hb
    | true =>
      simp only [d28454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28455 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28456 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28457 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28458 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28459 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67798 (p : Pattern) (ha : d28468 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28454 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67792 q ha hb
    | true =>
      simp only [d28454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28455 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28456 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28457 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28458 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28468 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67799 (p : Pattern) (ha : d28522 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28513 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67778 q ha hb
  have h2 (q : Pattern) (ha : d28137 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67778 q ha hb
    | true =>
      simp only [d28137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28514 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28138 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28515 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28516 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28516, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28516, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28517 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67779 q ha hb
  have h9 (q : Pattern) (ha : d28142 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67779 q ha hb
    | true =>
      simp only [d28142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28518 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28143 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28519 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28520 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28520, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28520, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d28521 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28498 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
  have h16 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d28499 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d28500 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d28501 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d28507 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d28522 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67800 (p : Pattern) (ha : d28559 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28554 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
  have h2 (q : Pattern) (ha : d28182 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
    | true =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28555 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28183 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28556 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28557 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28557, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28557, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d28558 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28531 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
  have h11 (q : Pattern) (ha : d28168 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
    | true =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28532 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28169 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28533 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28534 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28534, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28534, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h16 (q : Pattern) (ha : d28535 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h17 (q : Pattern) (ha : d28559 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67801 (p : Pattern) (ha : d28565 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28560 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67800 q ha hb
  have h2 (q : Pattern) (ha : d28561 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28562 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28563 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28564 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28565 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67802 (p : Pattern) (ha : d28672 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28566 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67801 q ha hb
    | true =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28567 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28669 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28670 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28671 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28672 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67803 (p : Pattern) (ha : d28678 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28673 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67802 q ha hb
    | true =>
      simp only [d28673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28674 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28675 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28676 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28677 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28678 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67804 (p : Pattern) (ha : d28228 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28201 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28227 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28228 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67805 (p : Pattern) (ha : d28230 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28205 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28229 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28230 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67806 (p : Pattern) (ha : d28237 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28235 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28236 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28237 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67807 (p : Pattern) (ha : d28240 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28238 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28239 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28240 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67808 (p : Pattern) (ha : d28244 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28097 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d28098 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28244 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro67809 (p : Pattern) (ha : d28249 p = 1) (hb : d171299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d28098 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d28098, d171299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28249 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro67810 (p : Pattern) (ha : d28256 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28245 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67808 q ha hb
    | true =>
      simp only [d28245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28246 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28247 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28248 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28248, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28248, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28250 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67809 q ha hb
    | true =>
      simp only [d28250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28251 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28252 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28253 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28253, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28253, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d28254 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28120 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28121 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d28255 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28256 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67811 (p : Pattern) (ha : d28260 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28120 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28121 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28121, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28128 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d28129 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28129, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d28130 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d28147 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28260 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67812 (p : Pattern) (ha : d28266 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28257 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67810 q ha hb
    | true =>
      simp only [d28257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
  have h2 (q : Pattern) (ha : d28258 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28259 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28261 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
    | true =>
      simp only [d28261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67811 q ha hb
  have h5 (q : Pattern) (ha : d28262 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28263 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28264 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28149 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
    | true =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
  have h9 (q : Pattern) (ha : d28150 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28151 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28174 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67783 q ha hb
  have h12 (q : Pattern) (ha : d28175 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28176 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28177 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28265 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28266 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro67813 (p : Pattern) (ha : d28277 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28267 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67812 q ha hb
    | true =>
      simp only [d28267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28268 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28272 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67794 q ha hb
    | true =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28273 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28274 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28275 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28276 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28277 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67814 (p : Pattern) (ha : d28398 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28182 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
    | true =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28183 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28184 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d28185 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28185, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28185, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28186 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28398 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro67815 (p : Pattern) (ha : d28404 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28149 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67777 q ha hb
    | true =>
      simp only [d28149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
  have h2 (q : Pattern) (ha : d28150 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28151 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28174 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67783 q ha hb
  have h5 (q : Pattern) (ha : d28175 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28176 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28177 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28399 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67780 q ha hb
    | true =>
      simp only [d28399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67814 q ha hb
  have h9 (q : Pattern) (ha : d28400 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28401 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28402 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28403 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28404 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro67816 (p : Pattern) (ha : d28410 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28405 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67815 q ha hb
    | true =>
      simp only [d28405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28406 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28407 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28408 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28409 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28410 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67817 (p : Pattern) (ha : d171300 p = 1) (hb : d212356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28231 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67804 q ha hb
    | true =>
      simp only [d28231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67805 q ha hb
  have h2 (q : Pattern) (ha : d28232 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28233 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28234 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28241 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67806 q ha hb
    | true =>
      simp only [d28241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67807 q ha hb
  have h6 (q : Pattern) (ha : d28242 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28243 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28282 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67813 q ha hb
    | true =>
      simp only [d28282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67795 q ha hb
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d28411 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67816 q ha hb
    | true =>
      simp only [d28411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28412 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67818 (p : Pattern) (ha : d28417 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28201 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28227 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28417 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67819 (p : Pattern) (ha : d28418 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28205 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28229 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28418 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67820 (p : Pattern) (ha : d28423 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28194 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67786 q ha hb
    | true =>
      simp only [d28194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28195 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28200 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28235 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28236 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28423 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67821 (p : Pattern) (ha : d28424 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28204 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28238 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28239 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28424 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67822 (p : Pattern) (ha : d28428 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28267 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67812 q ha hb
    | true =>
      simp only [d28267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28268 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28272 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67794 q ha hb
    | true =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28273 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28274 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28275 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28276 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28428 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67823 (p : Pattern) (ha : d28429 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28272 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67794 q ha hb
    | true =>
      simp only [d28272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28273 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28198 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67787 q ha hb
    | true =>
      simp only [d28198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28199 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28278 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28279 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28280 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28429 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67824 (p : Pattern) (ha : d28435 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28405 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67815 q ha hb
    | true =>
      simp only [d28405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28406 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28407 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28408 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28409 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28435 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67825 (p : Pattern) (ha : d171300 p = 1) (hb : d212361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28231 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67804 q ha hb
    | true =>
      simp only [d28231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67805 q ha hb
  have h2 (q : Pattern) (ha : d28232 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28233 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28234 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28241 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67806 q ha hb
    | true =>
      simp only [d28241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67807 q ha hb
  have h6 (q : Pattern) (ha : d28242 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28243 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28282 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67813 q ha hb
    | true =>
      simp only [d28282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67795 q ha hb
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d212352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d28411 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67816 q ha hb
    | true =>
      simp only [d28411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28412 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d212355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28419 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67818 q ha hb
    | true =>
      simp only [d28419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67819 q ha hb
  have h16 (q : Pattern) (ha : d28420 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28421 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28422 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28425 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67820 q ha hb
    | true =>
      simp only [d28425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67821 q ha hb
  have h20 (q : Pattern) (ha : d28426 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28427 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28430 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67822 q ha hb
    | true =>
      simp only [d28430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67823 q ha hb
  have h23 (q : Pattern) (ha : d171300 q = 1) (hb : d212357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d28436 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67824 q ha hb
    | true =>
      simp only [d28436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d28437 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d28437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d171300 q = 1) (hb : d212358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d171300 q = 1) (hb : d212359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d212359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d171300 q = 1) (hb : d212360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d212360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d171300 q = 1) (hb : d212361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d212361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro67826 (p : Pattern) (ha : d171300 p = 1) (hb : d212368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28430 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67822 q ha hb
    | true =>
      simp only [d28430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67823 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d28436 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67824 q ha hb
    | true =>
      simp only [d28436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28437 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67827 (p : Pattern) (ha : d28488 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28474 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67808 q ha hb
  have h2 (q : Pattern) (ha : d28245 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67808 q ha hb
    | true =>
      simp only [d28245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28475 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28246 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28476 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28477 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28477, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28477, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28478 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67809 q ha hb
  have h9 (q : Pattern) (ha : d28250 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67809 q ha hb
    | true =>
      simp only [d28250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28479 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28251 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28480 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28481 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28481, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28481, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d28482 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d28483 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
  have h17 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28484 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d28485 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28486 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h22 (q : Pattern) (ha : d28487 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d28488 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67828 (p : Pattern) (ha : d28503 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28489 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67773 q ha hb
  have h2 (q : Pattern) (ha : d28104 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67773 q ha hb
    | true =>
      simp only [d28104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28490 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28105 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28491 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28492 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28492, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28492, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28493 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67774 q ha hb
  have h9 (q : Pattern) (ha : d28109 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67774 q ha hb
    | true =>
      simp only [d28109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28494 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28110 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28495 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28496 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28496, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28496, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d28497 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28483 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
  have h16 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d28484 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d28485 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d28486 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h21 (q : Pattern) (ha : d28498 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
  have h22 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d28499 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d28500 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d28501 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h27 (q : Pattern) (ha : d28502 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d28503 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro67829 (p : Pattern) (ha : d28508 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28483 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
  have h2 (q : Pattern) (ha : d28118 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67775 q ha hb
    | true =>
      simp only [d28118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28484 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28119 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28485 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28486 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28486, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28498 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
  have h9 (q : Pattern) (ha : d28126 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67776 q ha hb
    | true =>
      simp only [d28126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28499 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28127 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28500 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28501 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28501, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h14 (q : Pattern) (ha : d28502 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d28507 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28508 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67830 (p : Pattern) (ha : d28536 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28526 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67781 q ha hb
  have h2 (q : Pattern) (ha : d28156 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67781 q ha hb
    | true =>
      simp only [d28156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28527 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28157 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28528 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28529 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28529, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28529, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d28530 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28531 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
  have h11 (q : Pattern) (ha : d28168 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67782 q ha hb
    | true =>
      simp only [d28168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28532 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28169 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28533 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28534 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28534, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d28534, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h16 (q : Pattern) (ha : d28535 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h17 (q : Pattern) (ha : d28536 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67831 (p : Pattern) (ha : d28542 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28504 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67827 q ha hb
    | true =>
      simp only [d28504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
  have h2 (q : Pattern) (ha : d28505 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28506 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28509 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
    | true =>
      simp only [d28509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67829 q ha hb
  have h5 (q : Pattern) (ha : d28510 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28511 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28512 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28523 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
    | true =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
  have h9 (q : Pattern) (ha : d28524 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28525 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28537 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67830 q ha hb
  have h12 (q : Pattern) (ha : d28538 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28539 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28540 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28541 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28542 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro67832 (p : Pattern) (ha : d28547 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
    | true =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67830 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28545 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28546 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28547 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro67833 (p : Pattern) (ha : d28553 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28543 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67831 q ha hb
    | true =>
      simp only [d28543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28544 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28548 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67832 q ha hb
    | true =>
      simp only [d28548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28549 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28550 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28551 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28552 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28553 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67834 (p : Pattern) (ha : d28571 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28548 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67832 q ha hb
    | true =>
      simp only [d28548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28549 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28566 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67801 q ha hb
    | true =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28567 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28568 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28569 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28570 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28571 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67835 (p : Pattern) (ha : d28649 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28554 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
  have h2 (q : Pattern) (ha : d28182 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67784 q ha hb
    | true =>
      simp only [d28182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28555 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28183 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28556 q = 1) (hb : d171299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d28557 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28557, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28557, d171300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d28558 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28649 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro67836 (p : Pattern) (ha : d28655 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
    | true =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67830 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28650 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67835 q ha hb
  have h9 (q : Pattern) (ha : d28651 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28652 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28653 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d28654 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28655 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro67837 (p : Pattern) (ha : d28661 p = 1) (hb : d171300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28656 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67836 q ha hb
    | true =>
      simp only [d28656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28657 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28658 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28659 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28660 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28661 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67838 (p : Pattern) (ha : d171300 p = 1) (hb : d212378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28572 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67833 q ha hb
    | true =>
      simp only [d28572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67834 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d28662 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67837 q ha hb
    | true =>
      simp only [d28662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28663 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67839 (p : Pattern) (ha : d171300 p = 1) (hb : d212384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28214 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67790 q ha hb
  have h2 (q : Pattern) (ha : d28215 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28224 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67790 q ha hb
    | true =>
      simp only [d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67793 q ha hb
  have h4 (q : Pattern) (ha : d28225 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28226 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d28226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67817 q ha hb
    | true =>
      simp only [d212362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67825 q ha hb
  have h7 (q : Pattern) (ha : d28460 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67796 q ha hb
    | true =>
      simp only [d28460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67797 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d212364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d212365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67826 q ha hb
  have h12 (q : Pattern) (ha : d28469 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67798 q ha hb
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d212372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d171300 q = 1) (hb : d212373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d171300 q = 1) (hb : d212379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67838 q ha hb
  have h18 (q : Pattern) (ha : d28679 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67803 q ha hb
  have h19 (q : Pattern) (ha : d171300 q = 1) (hb : d212380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d212380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d171300 q = 1) (hb : d212381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d212381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d171300 q = 1) (hb : d212382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d212382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d171300 q = 1) (hb : d212383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d212383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d171300 q = 1) (hb : d212384 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d212384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67840 (p : Pattern) (ha : d171300 p = 1) (hb : d212390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212385 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67839 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212386 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212387 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212388 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212390 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67841 (p : Pattern) (ha : d171300 p = 1) (hb : d212396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38232 q ha hb
    | true =>
      simp only [d128269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38277 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38329 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38398 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212348 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67772 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212349 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212350 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212351 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d212351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212391 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67840 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212392 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212393 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212394 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212395 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d171300 q = 1) (hb : d212396 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro67842 (p : Pattern) (ha : d171300 p = 1) (hb : d212402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212397 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67841 q ha hb
    | true =>
      simp only [d212397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212398 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212399 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212400 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212401 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212402 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67843 (p : Pattern) (ha : d171300 p = 1) (hb : d212408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212403 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67842 q ha hb
    | true =>
      simp only [d212403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212404 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212405 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212406 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212407 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212408 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67844 (p : Pattern) (ha : d171300 p = 1) (hb : d212414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212409 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67843 q ha hb
    | true =>
      simp only [d212409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212410 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212411 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212412 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212413 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212414 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67845 (p : Pattern) (ha : d171300 p = 1) (hb : d212420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212415 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67844 q ha hb
    | true =>
      simp only [d212415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212416 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212417 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212418 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212419 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212420 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67846 (p : Pattern) (ha : d171300 p = 1) (hb : d212426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212421 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67845 q ha hb
    | true =>
      simp only [d212421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212422 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212423 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212424 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212425 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212426 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67847 (p : Pattern) (ha : d171300 p = 1) (hb : d212432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212427 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67846 q ha hb
    | true =>
      simp only [d212427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212428 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212429 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212430 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212431 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212432 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67848 (p : Pattern) (ha : d171300 p = 1) (hb : d212438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212433 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67847 q ha hb
    | true =>
      simp only [d212433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212434 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212435 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212436 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212437 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212438 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67849 (p : Pattern) (ha : d171300 p = 1) (hb : d212441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27604 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67722 q ha hb
    | true =>
      simp only [d27604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67723 q ha hb
  have h2 (q : Pattern) (ha : d27605 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27606 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27607 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27608 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro67850 (p : Pattern) (ha : d171300 p = 1) (hb : d212448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27923 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67760 q ha hb
    | true =>
      simp only [d27923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
  have h2 (q : Pattern) (ha : d27924 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27925 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27937 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d27937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67762 q ha hb
  have h5 (q : Pattern) (ha : d27938 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27939 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27940 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27960 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67730 q ha hb
    | true =>
      simp only [d27960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67731 q ha hb
  have h9 (q : Pattern) (ha : d27961 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27962 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27963 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212447 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212448 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67851 (p : Pattern) (ha : d171300 p = 1) (hb : d212454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212449 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67850 q ha hb
    | true =>
      simp only [d212449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212450 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27966 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67732 q ha hb
    | true =>
      simp only [d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27967 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212451 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212452 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212453 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67852 (p : Pattern) (ha : d171300 p = 1) (hb : d212460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67851 q ha hb
    | true =>
      simp only [d212455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67733 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67853 (p : Pattern) (ha : d171300 p = 1) (hb : d212466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27610 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67721 q ha hb
    | true =>
      simp only [d27610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67724 q ha hb
  have h2 (q : Pattern) (ha : d27611 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212439 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212440 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212442 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67849 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212443 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212444 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212445 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212446 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67852 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212464 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212465 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212466 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67854 (p : Pattern) (ha : d171300 p = 1) (hb : d212472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212467 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67853 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212468 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212469 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212470 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212471 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67855 (p : Pattern) (ha : d171300 p = 1) (hb : d212479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28218 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67791 q ha hb
    | true =>
      simp only [d28218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67792 q ha hb
  have h2 (q : Pattern) (ha : d28219 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28220 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28221 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28222 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro67856 (p : Pattern) (ha : d171300 p = 1) (hb : d212486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28523 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67828 q ha hb
    | true =>
      simp only [d28523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
  have h2 (q : Pattern) (ha : d28524 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28525 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28537 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67830 q ha hb
  have h5 (q : Pattern) (ha : d28538 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28539 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28540 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28560 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67799 q ha hb
    | true =>
      simp only [d28560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67800 q ha hb
  have h9 (q : Pattern) (ha : d28561 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28562 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28563 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212485 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d212485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212486 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67857 (p : Pattern) (ha : d171300 p = 1) (hb : d212492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67856 q ha hb
    | true =>
      simp only [d212487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28566 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67801 q ha hb
    | true =>
      simp only [d28566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28567 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67858 (p : Pattern) (ha : d171300 p = 1) (hb : d212498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212493 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67857 q ha hb
    | true =>
      simp only [d212493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67802 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212494 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212495 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212496 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212497 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212498 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67859 (p : Pattern) (ha : d171300 p = 1) (hb : d212504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28224 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67790 q ha hb
    | true =>
      simp only [d28224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67793 q ha hb
  have h2 (q : Pattern) (ha : d28225 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d212477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67855 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212481 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212482 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d212482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212483 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d212483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212484 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212499 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67858 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212500 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212501 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d212501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212502 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d212502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212503 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d212503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212504 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d212504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67860 (p : Pattern) (ha : d171300 p = 1) (hb : d212510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212505 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67859 q ha hb
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212506 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212507 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212508 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212509 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212510 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d212510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67861 (p : Pattern) (ha : d171300 p = 1) (hb : d212516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d171102 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38550 q ha hb
    | true =>
      simp only [d171102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38554 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d171129 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38558 q ha hb
  have h3 (q : Pattern) (ha : d171130 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d171165 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38564 q ha hb
  have h5 (q : Pattern) (ha : d171166 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d171167 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d171300 q = 1) (hb : d212473 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67854 q ha hb
  have h8 (q : Pattern) (ha : d171300 q = 1) (hb : d212474 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d171300 q = 1) (hb : d212475 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d171300 q = 1) (hb : d212476 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d212476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d171300 q = 1) (hb : d212511 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67860 q ha hb
  have h12 (q : Pattern) (ha : d171300 q = 1) (hb : d212512 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d171300 q = 1) (hb : d212513 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d171300 q = 1) (hb : d212514 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d212514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d171300 q = 1) (hb : d212515 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d212515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d171300 q = 1) (hb : d212516 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d212516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro67862 (p : Pattern) (ha : d171300 p = 1) (hb : d212522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212517 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67861 q ha hb
    | true =>
      simp only [d212517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212518 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212519 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212520 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212521 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212522 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67863 (p : Pattern) (ha : d171300 p = 1) (hb : d212528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212523 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67862 q ha hb
    | true =>
      simp only [d212523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212524 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212525 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212526 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212527 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212528 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67864 (p : Pattern) (ha : d171300 p = 1) (hb : d212534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212529 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67863 q ha hb
    | true =>
      simp only [d212529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212530 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212531 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212532 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212533 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212534 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67865 (p : Pattern) (ha : d171300 p = 1) (hb : d212540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212535 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67864 q ha hb
    | true =>
      simp only [d212535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212536 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212537 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212538 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212539 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212540 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67866 (p : Pattern) (ha : d171300 p = 1) (hb : d212546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212541 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67865 q ha hb
    | true =>
      simp only [d212541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212542 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212543 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212544 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212545 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212546 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67867 (p : Pattern) (ha : d171300 p = 1) (hb : d212552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212547 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67866 q ha hb
    | true =>
      simp only [d212547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212548 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212549 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212550 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212551 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212552 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67868 (p : Pattern) (ha : d171300 p = 1) (hb : d212558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d171300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d171300 q = 1) (hb : d212553 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67867 q ha hb
    | true =>
      simp only [d212553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d171300 q = 1) (hb : d212554 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d212554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d171300 q = 1) (hb : d212555 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d212555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d171300 q = 1) (hb : d212556 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d212556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d171300 q = 1) (hb : d212557 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d212557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d171300 q = 1) (hb : d212558 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d212558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67869 (p : Pattern) (ha : d132 p = 1) (hb : d216468 p = 1) : d5011 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d16 q = 1) (hb : d216468 q = 1) : d16 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131 q = 1) (hb : d216468 q = 1) : d5010 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17 q = 1) (hb : d216468 q = 1) : d17 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d132 q = 1) (hb : d216468 q = 1) : d5011 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d5011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132, d5011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67870 (p : Pattern) (ha : d138 p = 1) (hb : d267844 p = 1) : d36007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d267844 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d267844 q = 1) : d36005 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d267844 q = 1) : d36006 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d267844 q = 1) : d23 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d138 q = 1) (hb : d267844 q = 1) : d36007 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d36007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138, d36007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67871 (p : Pattern) (ha : d144 p = 1) (hb : d267844 p = 1) : d36013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d267844 q = 1) : d36008 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
    | true =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d267844 q = 1) : d36009 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d267844 q = 1) : d36010 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d267844 q = 1) : d36011 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d267844 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d267844 q = 1) : d36012 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d36012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d36012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d267844 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d267844 q = 1) : d36013 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d36013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d36013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67872 (p : Pattern) (ha : d150 p = 1) (hb : d267844 p = 1) : d36019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d267844 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d267844 q = 1) : d36014 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
    | true =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d267844 q = 1) : d36015 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d267844 q = 1) : d36016 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d267844 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d267844 q = 1) : d36017 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d267844 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d267844 q = 1) : d36018 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d36018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d36018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d267844 q = 1) : d36019 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d36019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d36019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro67873 (p : Pattern) (ha : d203 p = 1) (hb : d267844 p = 1) : d36032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d267844 q = 1) : d36023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d267844 q = 1) : d36024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d267844 q = 1) : d36032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d36032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d36032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67874 (p : Pattern) (ha : d4349 p = 1) (hb : d267844 p = 1) : d269927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d267844 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d267844 q = 1) : d36033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
    | true =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d267844 q = 1) : d269916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d267844 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d267844 q = 1) : d269917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d267844 q = 1) : d269925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d269925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d267844 q = 1) : d269926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d269926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d267844 q = 1) : d269927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d269927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67875 (p : Pattern) (ha : d231 p = 1) (hb : d267844 p = 1) : d36056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d267844 q = 1) : d36051 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d267844 q = 1) : d36008 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
    | true =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d267844 q = 1) : d36052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d267844 q = 1) : d36009 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d267844 q = 1) : d36053 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d267844 q = 1) : d36054 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d267844 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d267844 q = 1) : d36055 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d36055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d36055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d267844 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d267844 q = 1) : d36056 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d36056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d36056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67876 (p : Pattern) (ha : d237 p = 1) (hb : d267844 p = 1) : d36062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d267844 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d267844 q = 1) : d36057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
    | true =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d267844 q = 1) : d36058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d267844 q = 1) : d36059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d267844 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d267844 q = 1) : d36060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d267844 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d267844 q = 1) : d36061 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d36061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d36061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d267844 q = 1) : d36062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d36062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d36062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro67877 (p : Pattern) (ha : d243 p = 1) (hb : d267844 p = 1) : d36068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d267844 q = 1) : d36063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67876 q ha hb
    | true =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d267844 q = 1) : d36064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d267844 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d267844 q = 1) : d36065 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d36065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d36065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d267844 q = 1) : d36066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d36066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d36066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d267844 q = 1) : d36067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d36067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d36067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d267844 q = 1) : d36068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d36068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d36068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67878 (p : Pattern) (ha : d4359 p = 1) (hb : d267844 p = 1) : d269937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d267844 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d267844 q = 1) : d36069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67877 q ha hb
    | true =>
      simp only [d244, d36069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d267844 q = 1) : d269933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d269933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d267844 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d267844 q = 1) : d269934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d269934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d267844 q = 1) : d269935 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d269935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d267844 q = 1) : d269936 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d269936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d267844 q = 1) : d269937 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d269937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67879 (p : Pattern) (ha : d156 p = 1) (hb : d267844 p = 1) : d36025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d267844 q = 1) : d36023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d267844 q = 1) : d36024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d36024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d267844 q = 1) : d36025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d36025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d36025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67880 (p : Pattern) (ha : d51643 p = 1) (hb : d267844 p = 1) : d269915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d267844 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d267844 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d267844 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d267844 q = 1) : d36026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
    | true =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d267844 q = 1) : d269911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d267844 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d267844 q = 1) : d269912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d267844 q = 1) : d269913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d267844 q = 1) : d269914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d267844 q = 1) : d269915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d269915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67881 (p : Pattern) (ha : d51646 p = 1) (hb : d267844 p = 1) : d269920 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d267844 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d267844 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d267844 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d267844 q = 1) : d36026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
    | true =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d267844 q = 1) : d269911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d269911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d267844 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d267844 q = 1) : d269912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d269912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d267844 q = 1) : d269913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d269913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d267844 q = 1) : d269914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d269914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d267844 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d267844 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d267844 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d267844 q = 1) : d36033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
    | true =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d267844 q = 1) : d269916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d269916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d267844 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d267844 q = 1) : d269917 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d269917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d267844 q = 1) : d269918 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d269918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d267844 q = 1) : d269919 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d269919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d267844 q = 1) : d269920 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d269920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67882 (p : Pattern) (ha : d51652 p = 1) (hb : d267844 p = 1) : d269943 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d267844 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d267844 q = 1) : d269921 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67880 q ha hb
    | true =>
      simp only [d51647, d269921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67881 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d267844 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d267844 q = 1) : d269922 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d269922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d267844 q = 1) : d269923 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d269923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d267844 q = 1) : d269924 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d269924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d267844 q = 1) : d269928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d269928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67874 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d267844 q = 1) : d269929 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d269929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d267844 q = 1) : d269930 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d269930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d267844 q = 1) : d269931 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d269931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d267844 q = 1) : d269932 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d269932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d267844 q = 1) : d269938 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d269938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67878 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d267844 q = 1) : d269939 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d269939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d267844 q = 1) : d269940 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d269940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d267844 q = 1) : d269941 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d269941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d267844 q = 1) : d269942 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d269942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d267844 q = 1) : d269943 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d269943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67883 (p : Pattern) (ha : d284 p = 1) (hb : d267844 p = 1) : d36090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d267844 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d267844 q = 1) : d36026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
    | true =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d267844 q = 1) : d36086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d267844 q = 1) : d36087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d267844 q = 1) : d36088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d267844 q = 1) : d36089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d267844 q = 1) : d36090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d36090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d36090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67884 (p : Pattern) (ha : d291 p = 1) (hb : d267844 p = 1) : d36097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d267844 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d267844 q = 1) : d36026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
    | true =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d267844 q = 1) : d36086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d267844 q = 1) : d36087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d267844 q = 1) : d36088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d267844 q = 1) : d36089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d267844 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d267844 q = 1) : d36033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
    | true =>
      simp only [d204, d36033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d267844 q = 1) : d36093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d36093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d267844 q = 1) : d36094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d36094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d267844 q = 1) : d36095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d36095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d267844 q = 1) : d36096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d36096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d267844 q = 1) : d36097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d36097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d36097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67885 (p : Pattern) (ha : d397 p = 1) (hb : d267844 p = 1) : d36201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d267844 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d267844 q = 1) : d36026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
    | true =>
      simp only [d157, d36026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d267844 q = 1) : d36086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d36086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d267844 q = 1) : d36087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d36087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d267844 q = 1) : d36088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d36088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d267844 q = 1) : d36089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d36089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d267844 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d267844 q = 1) : d36201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d36201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d36201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67886 (p : Pattern) (ha : d296 p = 1) (hb : d267844 p = 1) : d36102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d267844 q = 1) : d36023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d267844 q = 1) : d36101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d267844 q = 1) : d36102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d36102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d36102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67887 (p : Pattern) (ha : d303 p = 1) (hb : d267844 p = 1) : d36109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d267844 q = 1) : d36107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d267844 q = 1) : d36108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d267844 q = 1) : d36109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d36109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d36109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67888 (p : Pattern) (ha : d4736 p = 1) (hb : d267844 p = 1) : d36172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d267844 q = 1) : d36169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d267844 q = 1) : d36170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d267844 q = 1) : d36171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d267844 q = 1) : d36172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d36172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d36172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67889 (p : Pattern) (ha : d312 p = 1) (hb : d216468 p = 1) : d36114 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d311 q = 1) (hb : d216468 q = 1) : d36113 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d311, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16 q = 1) (hb : d216468 q = 1) : d16 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d131 q = 1) (hb : d216468 q = 1) : d5010 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d312 q = 1) (hb : d216468 q = 1) : d36114 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d36114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312, d36114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67890 (p : Pattern) (ha : d318 p = 1) (hb : d267844 p = 1) : d36120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d267844 q = 1) : d36118 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d267844 q = 1) : d36119 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21 q = 1) (hb : d267844 q = 1) : d21 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d136 q = 1) (hb : d267844 q = 1) : d36005 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137 q = 1) (hb : d267844 q = 1) : d36006 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d318 q = 1) (hb : d267844 q = 1) : d36120 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d36120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318, d36120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67891 (p : Pattern) (ha : d9381 p = 1) (hb : d267844 p = 1) : d36126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d267844 q = 1) : d9455 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d9455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d267844 q = 1) : d9456 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d9456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d9456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d267844 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9381 q = 1) (hb : d267844 q = 1) : d36126 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d36126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9381, d36126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67892 (p : Pattern) (ha : d15966 p = 1) (hb : d267844 p = 1) : d36132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d267844 q = 1) : d36121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
    | true =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d267844 q = 1) : d36122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d267844 q = 1) : d36123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d267844 q = 1) : d36124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d267844 q = 1) : d36008 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
    | true =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d267844 q = 1) : d36009 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d267844 q = 1) : d36010 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d36010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d267844 q = 1) : d36011 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d36011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d267844 q = 1) : d36125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d36125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d36125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d267844 q = 1) : d36129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d267844 q = 1) : d36130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d267844 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d267844 q = 1) : d36131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d267844 q = 1) : d36132 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d36132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d36132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67893 (p : Pattern) (ha : d15972 p = 1) (hb : d267844 p = 1) : d36138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d267844 q = 1) : d36133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67892 q ha hb
    | true =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d267844 q = 1) : d36134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d267844 q = 1) : d36135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d267844 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d267844 q = 1) : d36014 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
    | true =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d267844 q = 1) : d36015 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d267844 q = 1) : d36016 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d267844 q = 1) : d36136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d267844 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d267844 q = 1) : d36017 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d36017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d267844 q = 1) : d36137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d36137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d36137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d267844 q = 1) : d36138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d36138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d36138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro67894 (p : Pattern) (ha : d15978 p = 1) (hb : d267844 p = 1) : d36144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d267844 q = 1) : d36139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67893 q ha hb
    | true =>
      simp only [d15973, d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d267844 q = 1) : d36140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d267844 q = 1) : d36141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d267844 q = 1) : d36142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d267844 q = 1) : d36143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d267844 q = 1) : d36144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d36144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d36144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67895 (p : Pattern) (ha : d128195 p = 1) (hb : d267844 p = 1) : d269953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d267844 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d267844 q = 1) : d36103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67886 q ha hb
    | true =>
      simp only [d297, d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d267844 q = 1) : d36104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d267844 q = 1) : d36105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d267844 q = 1) : d36106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d267844 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d267844 q = 1) : d36110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67887 q ha hb
    | true =>
      simp only [d304, d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d267844 q = 1) : d36111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d267844 q = 1) : d36112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d267844 q = 1) : d36145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67894 q ha hb
    | true =>
      simp only [d15979, d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d267844 q = 1) : d269949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d267844 q = 1) : d36173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67888 q ha hb
    | true =>
      simp only [d4737, d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d267844 q = 1) : d36174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d267844 q = 1) : d269950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d267844 q = 1) : d269951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d267844 q = 1) : d269952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d267844 q = 1) : d269953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d269953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro67896 (p : Pattern) (ha : d376 p = 1) (hb : d267844 p = 1) : d36179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d267844 q = 1) : d36023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d36023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d267844 q = 1) : d36101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d36101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d267844 q = 1) : d36179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d36179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d36179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67897 (p : Pattern) (ha : d381 p = 1) (hb : d267844 p = 1) : d36184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d267844 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d267844 q = 1) : d36022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d36022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d267844 q = 1) : d36107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d36107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d267844 q = 1) : d36108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d36108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d267844 q = 1) : d36184 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d36184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d36184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67898 (p : Pattern) (ha : d5355 p = 1) (hb : d267844 p = 1) : d36193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d267844 q = 1) : d36169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d36169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d267844 q = 1) : d36170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d36170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d267844 q = 1) : d36171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d36171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d267844 q = 1) : d36193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d36193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d36193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67899 (p : Pattern) (ha : d15985 p = 1) (hb : d267844 p = 1) : d36188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d267844 q = 1) : d36139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67893 q ha hb
    | true =>
      simp only [d15973, d36139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d267844 q = 1) : d36140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d36140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d267844 q = 1) : d36020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67872 q ha hb
    | true =>
      simp only [d151, d36020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d267844 q = 1) : d36021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d36021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d267844 q = 1) : d36141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d36141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d267844 q = 1) : d36142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d36142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d267844 q = 1) : d36143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d36143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d267844 q = 1) : d36188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d36188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d36188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67900 (p : Pattern) (ha : d128200 p = 1) (hb : d267844 p = 1) : d269958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d267844 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d267844 q = 1) : d36103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67886 q ha hb
    | true =>
      simp only [d297, d36103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d267844 q = 1) : d36104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d36104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d267844 q = 1) : d36105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d36105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d267844 q = 1) : d36106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d36106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d267844 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d267844 q = 1) : d36110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67887 q ha hb
    | true =>
      simp only [d304, d36110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d267844 q = 1) : d36111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d36111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d267844 q = 1) : d36112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d36112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d267844 q = 1) : d36145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67894 q ha hb
    | true =>
      simp only [d15979, d36145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67879 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d267844 q = 1) : d269949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d269949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d267844 q = 1) : d36173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67888 q ha hb
    | true =>
      simp only [d4737, d36173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d267844 q = 1) : d36174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d36174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d267844 q = 1) : d269950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d269950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d267844 q = 1) : d269951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d269951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d267844 q = 1) : d269952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d269952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d267844 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d267844 q = 1) : d36180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d36180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67896 q ha hb
    | true =>
      simp only [d377, d36180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d267844 q = 1) : d36181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d36181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d36181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d267844 q = 1) : d36182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d36182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d36182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d267844 q = 1) : d36183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d36183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d36183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d267844 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d267844 q = 1) : d36185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d36185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67897 q ha hb
    | true =>
      simp only [d382, d36185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d267844 q = 1) : d36186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d36186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d36186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d267844 q = 1) : d36187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d36187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d36187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d267844 q = 1) : d36189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67899 q ha hb
    | true =>
      simp only [d15986, d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d267844 q = 1) : d269954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d267844 q = 1) : d36194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67898 q ha hb
    | true =>
      simp only [d5356, d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d267844 q = 1) : d36195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d267844 q = 1) : d269955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d267844 q = 1) : d269956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d269956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d267844 q = 1) : d269957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d269957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d267844 q = 1) : d269958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d269958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro67901 (p : Pattern) (ha : d128207 p = 1) (hb : d267844 p = 1) : d269965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d267844 q = 1) : d36189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67899 q ha hb
    | true =>
      simp only [d15986, d36189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67873 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d267844 q = 1) : d269954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d269954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d267844 q = 1) : d36194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67898 q ha hb
    | true =>
      simp only [d5356, d36194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d267844 q = 1) : d36195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d36195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d267844 q = 1) : d269955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d269955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d267844 q = 1) : d269963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d269963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d267844 q = 1) : d269964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d269964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d267844 q = 1) : d269965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d269965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d269965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67902 (p : Pattern) (ha : d5377 p = 1) (hb : d267844 p = 1) : d36261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d267844 q = 1) : d36063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67876 q ha hb
    | true =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d267844 q = 1) : d36064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d267844 q = 1) : d36258 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d36258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d36258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d267844 q = 1) : d36259 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d36259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d36259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d267844 q = 1) : d36260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d36260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d36260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d267844 q = 1) : d36261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d36261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d36261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67903 (p : Pattern) (ha : d16004 p = 1) (hb : d267844 p = 1) : d36224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d267844 q = 1) : d36214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d267844 q = 1) : d36121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
    | true =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d267844 q = 1) : d36215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d267844 q = 1) : d36122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d267844 q = 1) : d36216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d267844 q = 1) : d36217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d267844 q = 1) : d36051 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d36051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d267844 q = 1) : d36008 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67870 q ha hb
    | true =>
      simp only [d139, d36008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d267844 q = 1) : d36052 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d36052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d267844 q = 1) : d36009 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d36009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d267844 q = 1) : d36053 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d36053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d267844 q = 1) : d36054 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d36054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d267844 q = 1) : d36218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d36218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d36218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d267844 q = 1) : d36219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d267844 q = 1) : d36220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d267844 q = 1) : d36221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d267844 q = 1) : d36222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d267844 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d267844 q = 1) : d36223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d267844 q = 1) : d36224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d36224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d36224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro67904 (p : Pattern) (ha : d16010 p = 1) (hb : d267844 p = 1) : d36230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d267844 q = 1) : d36225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67903 q ha hb
    | true =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d267844 q = 1) : d36226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d267844 q = 1) : d36227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d267844 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d267844 q = 1) : d36057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
    | true =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d267844 q = 1) : d36058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d267844 q = 1) : d36059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d267844 q = 1) : d36228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d267844 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d267844 q = 1) : d36060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d36060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d267844 q = 1) : d36229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d36229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d36229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d267844 q = 1) : d36230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d36230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d36230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro67905 (p : Pattern) (ha : d16016 p = 1) (hb : d267844 p = 1) : d36236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d267844 q = 1) : d36231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d36231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67904 q ha hb
    | true =>
      simp only [d16011, d36231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d267844 q = 1) : d36232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d36232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d36232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d267844 q = 1) : d36063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67876 q ha hb
    | true =>
      simp only [d238, d36063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d267844 q = 1) : d36064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d36064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d267844 q = 1) : d36233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d36233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d36233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d267844 q = 1) : d36234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d36234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d36234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d267844 q = 1) : d36235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d36235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d36235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d267844 q = 1) : d36236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d36236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d36236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67906 (p : Pattern) (ha : d128217 p = 1) (hb : d267844 p = 1) : d269975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d267844 q = 1) : d36237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d36237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67905 q ha hb
    | true =>
      simp only [d16017, d36237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67877 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d267844 q = 1) : d269971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d269971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d269971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d267844 q = 1) : d36262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d36262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67902 q ha hb
    | true =>
      simp only [d5378, d36262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d267844 q = 1) : d36263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d36263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d36263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d267844 q = 1) : d269972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d269972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d269972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d267844 q = 1) : d269973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d269973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d269973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d267844 q = 1) : d269974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d269974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d269974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d267844 q = 1) : d269975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d269975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d269975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67907 (p : Pattern) (ha : d128223 p = 1) (hb : d267844 p = 1) : d269981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d267844 q = 1) : d36091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d36091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d36091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67883 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d267844 q = 1) : d36092 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d36092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d36092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d267844 q = 1) : d36098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67883 q ha hb
    | true =>
      simp only [d292, d36098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67884 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d267844 q = 1) : d36099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d36099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d267844 q = 1) : d36100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d36100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d36100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d267844 q = 1) : d269959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67895 q ha hb
    | true =>
      simp only [d128201, d269959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67900 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d267844 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d267844 q = 1) : d36202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d36202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67885 q ha hb
    | true =>
      simp only [d398, d36202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d267844 q = 1) : d269960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d269960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d267844 q = 1) : d269961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d269961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d269961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d267844 q = 1) : d269962 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d269962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d269962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d267844 q = 1) : d269966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d269966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d269966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67901 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d267844 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d267844 q = 1) : d269967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d269967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d269967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d267844 q = 1) : d269968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d269968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d269968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d267844 q = 1) : d269969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d269969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d269969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d267844 q = 1) : d269970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d269970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d269970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d267844 q = 1) : d269976 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d269976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d269976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67906 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d267844 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d267844 q = 1) : d269977 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d269977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d269977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d267844 q = 1) : d269978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d269978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d269978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d267844 q = 1) : d269979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d269979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d269979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d267844 q = 1) : d269980 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d269980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d269980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d267844 q = 1) : d269981 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d269981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d269981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro67908 (p : Pattern) (ha : d128229 p = 1) (hb : d267844 p = 1) : d269987 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d267844 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d267844 q = 1) : d269944 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d269944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67882 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d267844 q = 1) : d269945 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d269945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d267844 q = 1) : d269946 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d269946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d267844 q = 1) : d269947 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d269947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d267844 q = 1) : d269948 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d269948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d267844 q = 1) : d269982 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d269982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d269982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67907 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d267844 q = 1) : d269983 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d269983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d269983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d267844 q = 1) : d269984 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d269984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d269984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d267844 q = 1) : d269985 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d269985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d269985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d267844 q = 1) : d269986 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d269986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d269986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d267844 q = 1) : d269987 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d269987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d269987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro67909 (p : Pattern) (ha : d481 p = 1) (hb : d267844 p = 1) : d36286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d267844 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d267844 q = 1) : d36014 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
    | true =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d267844 q = 1) : d36015 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d267844 q = 1) : d36016 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d267844 q = 1) : d36280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d267844 q = 1) : d36285 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d36285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d36285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d267844 q = 1) : d36286 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d36286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d36286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67910 (p : Pattern) (ha : d491 p = 1) (hb : d267844 p = 1) : d36296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d267844 q = 1) : d36294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d267844 q = 1) : d36295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d267844 q = 1) : d36296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d36296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d36296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67911 (p : Pattern) (ha : d501 p = 1) (hb : d267844 p = 1) : d36306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d267844 q = 1) : d36294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d267844 q = 1) : d36295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d36295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d267844 q = 1) : d36306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d36306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d36306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67912 (p : Pattern) (ha : d644 p = 1) (hb : d267844 p = 1) : d36466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d267844 q = 1) : d36455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67910 q ha hb
    | true =>
      simp only [d633, d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d267844 q = 1) : d36456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d267844 q = 1) : d36457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d267844 q = 1) : d36458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d267844 q = 1) : d36459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d267844 q = 1) : d36461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67911 q ha hb
    | true =>
      simp only [d639, d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d267844 q = 1) : d36462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d267844 q = 1) : d36463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d267844 q = 1) : d36464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d267844 q = 1) : d36465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d267844 q = 1) : d36466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d36466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d36466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67913 (p : Pattern) (ha : d653 p = 1) (hb : d267844 p = 1) : d36475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d267844 q = 1) : d36461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67911 q ha hb
    | true =>
      simp only [d639, d36461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d267844 q = 1) : d36462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d36462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d267844 q = 1) : d36463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d36463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d267844 q = 1) : d36464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d36464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d267844 q = 1) : d36465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d36465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d267844 q = 1) : d36475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d36475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d36475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67914 (p : Pattern) (ha : d683 p = 1) (hb : d267844 p = 1) : d36518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d267844 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d267844 q = 1) : d36057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
    | true =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d267844 q = 1) : d36058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d267844 q = 1) : d36059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d267844 q = 1) : d36508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d267844 q = 1) : d36517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d36517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d36517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d267844 q = 1) : d36518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d36518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d36518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67915 (p : Pattern) (ha : d730 p = 1) (hb : d267844 p = 1) : d36574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d267844 q = 1) : d36519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67914 q ha hb
    | true =>
      simp only [d684, d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d267844 q = 1) : d36520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d267844 q = 1) : d36571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d36571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d36571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d267844 q = 1) : d36572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d36572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d36572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d267844 q = 1) : d36573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d36573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d36573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d267844 q = 1) : d36574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d36574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d36574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67916 (p : Pattern) (ha : d736 p = 1) (hb : d267844 p = 1) : d36580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d267844 q = 1) : d36575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d36575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67915 q ha hb
    | true =>
      simp only [d731, d36575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d267844 q = 1) : d36576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d36576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d36576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d267844 q = 1) : d36577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d36577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d36577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d267844 q = 1) : d36578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d36578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d36578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d267844 q = 1) : d36579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d36579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d36579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d267844 q = 1) : d36580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d36580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d36580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67917 (p : Pattern) (ha : d16036 p = 1) (hb : d267844 p = 1) : d36282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d267844 q = 1) : d36133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67892 q ha hb
    | true =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d267844 q = 1) : d36134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d267844 q = 1) : d36135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d267844 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d267844 q = 1) : d36014 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
    | true =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d267844 q = 1) : d36015 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d267844 q = 1) : d36016 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d267844 q = 1) : d36136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d267844 q = 1) : d36280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d36280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d267844 q = 1) : d36281 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d36281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d36281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d267844 q = 1) : d36282 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d36282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d36282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro67918 (p : Pattern) (ha : d16042 p = 1) (hb : d267844 p = 1) : d36292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d267844 q = 1) : d36290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d267844 q = 1) : d36291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d267844 q = 1) : d36292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d36292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d36292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67919 (p : Pattern) (ha : d16048 p = 1) (hb : d267844 p = 1) : d36302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d267844 q = 1) : d36297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67918 q ha hb
    | true =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67910 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d267844 q = 1) : d36298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d267844 q = 1) : d36299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d267844 q = 1) : d36300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d267844 q = 1) : d36301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d267844 q = 1) : d36302 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d36302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d36302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67920 (p : Pattern) (ha : d16051 p = 1) (hb : d267844 p = 1) : d36305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d267844 q = 1) : d36290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d267844 q = 1) : d36291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d36291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d267844 q = 1) : d36305 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d36305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d36305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67921 (p : Pattern) (ha : d16057 p = 1) (hb : d267844 p = 1) : d36312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d267844 q = 1) : d36297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67918 q ha hb
    | true =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67910 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d267844 q = 1) : d36298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d267844 q = 1) : d36299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d267844 q = 1) : d36300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d267844 q = 1) : d36301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d267844 q = 1) : d36307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67920 q ha hb
    | true =>
      simp only [d16052, d36307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67911 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d267844 q = 1) : d36308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d36308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d267844 q = 1) : d36309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d36309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d267844 q = 1) : d36310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d36310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d267844 q = 1) : d36311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d36311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d267844 q = 1) : d36312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d36312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d36312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67922 (p : Pattern) (ha : d16143 p = 1) (hb : d267844 p = 1) : d36460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d267844 q = 1) : d36297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67918 q ha hb
    | true =>
      simp only [d16043, d36297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67910 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d267844 q = 1) : d36298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d36298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d267844 q = 1) : d36299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d36299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d267844 q = 1) : d36300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d36300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d267844 q = 1) : d36301 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d36301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d267844 q = 1) : d36455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67910 q ha hb
    | true =>
      simp only [d633, d36455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d267844 q = 1) : d36456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d36456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d267844 q = 1) : d36457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d36457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d267844 q = 1) : d36458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d36458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d267844 q = 1) : d36459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d36459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d267844 q = 1) : d36460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d36460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d36460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67923 (p : Pattern) (ha : d514 p = 1) (hb : d267844 p = 1) : d36319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d267844 q = 1) : d36294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d267844 q = 1) : d36318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d267844 q = 1) : d36319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d36319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d36319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67924 (p : Pattern) (ha : d524 p = 1) (hb : d267844 p = 1) : d36329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d267844 q = 1) : d36327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d267844 q = 1) : d36328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d267844 q = 1) : d36329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d36329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d36329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67925 (p : Pattern) (ha : d16062 p = 1) (hb : d267844 p = 1) : d36317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d267844 q = 1) : d36290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d267844 q = 1) : d36316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d267844 q = 1) : d36317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d36317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d36317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67926 (p : Pattern) (ha : d16069 p = 1) (hb : d267844 p = 1) : d36326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d267844 q = 1) : d36324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d267844 q = 1) : d36325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d267844 q = 1) : d36326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d36326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d36326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67927 (p : Pattern) (ha : d530 p = 1) (hb : d216468 p = 1) : d36334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d529 q = 1) (hb : d216468 q = 1) : d36333 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d529, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d311 q = 1) (hb : d216468 q = 1) : d36113 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d311, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d530 q = 1) (hb : d216468 q = 1) : d36334 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d36334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d530, d36334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67928 (p : Pattern) (ha : d536 p = 1) (hb : d216468 p = 1) : d36114 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d534 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d535 q = 1) (hb : d216468 q = 1) : d36113 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d535, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d16 q = 1) (hb : d216468 q = 1) : d16 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131 q = 1) (hb : d216468 q = 1) : d5010 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131, d5010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d536 q = 1) (hb : d216468 q = 1) : d36114 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d536, d36114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d536, d36114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67929 (p : Pattern) (ha : d542 p = 1) (hb : d267844 p = 1) : d36340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d216468 q = 1) : d36335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67927 q ha hb
    | true =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d267844 q = 1) : d36336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d267844 q = 1) : d36337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d537 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67928 q ha hb
    | true =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d538 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d539 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d540 q = 1) (hb : d267844 q = 1) : d36338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d541 q = 1) (hb : d267844 q = 1) : d36339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316 q = 1) (hb : d267844 q = 1) : d36118 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d317 q = 1) (hb : d267844 q = 1) : d36119 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h20 (q : Pattern) (ha : d542 q = 1) (hb : d267844 q = 1) : d36340 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d36340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d542, d36340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro67930 (p : Pattern) (ha : d9457 p = 1) (hb : d267844 p = 1) : d36345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d267844 q = 1) : d36118 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d36118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d267844 q = 1) : d36119 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d36119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9456 q = 1) (hb : d267844 q = 1) : d9456 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9457 q = 1) (hb : d267844 q = 1) : d36345 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9457, d36345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9457, d36345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67931 (p : Pattern) (ha : d9467 p = 1) (hb : d267844 p = 1) : d36353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9464 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9464, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9465 q = 1) (hb : d267844 q = 1) : d36351 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d36351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9465, d36351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9466 q = 1) (hb : d267844 q = 1) : d36352 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d36352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9466, d36352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9456 q = 1) (hb : d267844 q = 1) : d9456 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9467 q = 1) (hb : d267844 q = 1) : d36353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d36353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9467, d36353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67932 (p : Pattern) (ha : d16077 p = 1) (hb : d267844 p = 1) : d36359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d267844 q = 1) : d36341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67929 q ha hb
    | true =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d267844 q = 1) : d36342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d267844 q = 1) : d36343 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d267844 q = 1) : d36344 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d267844 q = 1) : d36346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67930 q ha hb
    | true =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d267844 q = 1) : d36347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d267844 q = 1) : d36348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d267844 q = 1) : d36349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d267844 q = 1) : d36350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d267844 q = 1) : d36356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d267844 q = 1) : d36357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d267844 q = 1) : d36129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d267844 q = 1) : d36130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16076 q = 1) (hb : d267844 q = 1) : d36358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d36358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16076, d36358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16077 q = 1) (hb : d267844 q = 1) : d36359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d36359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16077, d36359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67933 (p : Pattern) (ha : d16081 p = 1) (hb : d267844 p = 1) : d36363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d267844 q = 1) : d36129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d36129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d267844 q = 1) : d36130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d36130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d267844 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d267844 q = 1) : d36131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d36131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d267844 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d267844 q = 1) : d36363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d36363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d36363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67934 (p : Pattern) (ha : d16087 p = 1) (hb : d267844 p = 1) : d36369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d267844 q = 1) : d36360 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d36360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67932 q ha hb
    | true =>
      simp only [d16078, d36360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67892 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d267844 q = 1) : d36361 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d36361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d36361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d267844 q = 1) : d36362 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d36362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d36362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d267844 q = 1) : d36364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d36364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67892 q ha hb
    | true =>
      simp only [d16082, d36364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67933 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d267844 q = 1) : d36365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d36365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d36365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d267844 q = 1) : d36366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d36366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d36366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d267844 q = 1) : d36367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d36367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d36367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d267844 q = 1) : d36133 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67892 q ha hb
    | true =>
      simp only [d15967, d36133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d267844 q = 1) : d36134 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d36134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d267844 q = 1) : d36135 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d36135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d267844 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d267844 q = 1) : d36014 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67871 q ha hb
    | true =>
      simp only [d145, d36014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d267844 q = 1) : d36015 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d36015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d267844 q = 1) : d36016 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d36016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d267844 q = 1) : d36136 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d36136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d267844 q = 1) : d36368 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d36368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d36368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d267844 q = 1) : d36369 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d36369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d36369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro67935 (p : Pattern) (ha : d16093 p = 1) (hb : d267844 p = 1) : d36375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d267844 q = 1) : d36370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67934 q ha hb
    | true =>
      simp only [d16088, d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d267844 q = 1) : d36371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d267844 q = 1) : d36372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d267844 q = 1) : d36373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d267844 q = 1) : d36374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d267844 q = 1) : d36375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d36375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d36375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67936 (p : Pattern) (ha : d16114 p = 1) (hb : d267844 p = 1) : d36423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d267844 q = 1) : d36420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d267844 q = 1) : d36421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d267844 q = 1) : d36422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d267844 q = 1) : d36423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d36423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d36423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67937 (p : Pattern) (ha : d128234 p = 1) (hb : d267844 p = 1) : d269992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d267844 q = 1) : d36320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67925 q ha hb
    | true =>
      simp only [d16063, d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67923 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d267844 q = 1) : d36321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d267844 q = 1) : d36322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d267844 q = 1) : d36323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d267844 q = 1) : d36330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67926 q ha hb
    | true =>
      simp only [d16070, d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67924 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d267844 q = 1) : d36331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d267844 q = 1) : d36332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d267844 q = 1) : d36376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67935 q ha hb
    | true =>
      simp only [d16094, d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67918 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d267844 q = 1) : d269988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d267844 q = 1) : d36424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67936 q ha hb
    | true =>
      simp only [d16115, d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d267844 q = 1) : d36425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d267844 q = 1) : d269989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d267844 q = 1) : d269990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d267844 q = 1) : d269991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d267844 q = 1) : d269992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d269992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67938 (p : Pattern) (ha : d610 p = 1) (hb : d267844 p = 1) : d36431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d267844 q = 1) : d36294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d36294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d267844 q = 1) : d36318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d36318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d267844 q = 1) : d36431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d36431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d36431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67939 (p : Pattern) (ha : d616 p = 1) (hb : d267844 p = 1) : d36437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d267844 q = 1) : d36293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d36293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d267844 q = 1) : d36327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d36327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d267844 q = 1) : d36328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d36328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d267844 q = 1) : d36437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d36437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d36437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67940 (p : Pattern) (ha : d16121 p = 1) (hb : d267844 p = 1) : d36430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d267844 q = 1) : d36290 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d36290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d267844 q = 1) : d36316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d36316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d267844 q = 1) : d36430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d36430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d36430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67941 (p : Pattern) (ha : d16126 p = 1) (hb : d267844 p = 1) : d36436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d267844 q = 1) : d36287 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67909 q ha hb
    | true =>
      simp only [d482, d36287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d267844 q = 1) : d36288 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d36288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d267844 q = 1) : d36289 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d36289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d267844 q = 1) : d36324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d36324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d267844 q = 1) : d36325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d36325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d267844 q = 1) : d36436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d36436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d36436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67942 (p : Pattern) (ha : d16130 p = 1) (hb : d267844 p = 1) : d36441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d267844 q = 1) : d36370 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67934 q ha hb
    | true =>
      simp only [d16088, d36370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d267844 q = 1) : d36371 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d36371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d267844 q = 1) : d36372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d36372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d267844 q = 1) : d36373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d36373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d267844 q = 1) : d36374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d36374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d267844 q = 1) : d36441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d36441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d36441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67943 (p : Pattern) (ha : d16135 p = 1) (hb : d267844 p = 1) : d36447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d267844 q = 1) : d36283 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67917 q ha hb
    | true =>
      simp only [d16037, d36283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d267844 q = 1) : d36284 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d36284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d267844 q = 1) : d36420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d36420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d267844 q = 1) : d36421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d36421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d267844 q = 1) : d36422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d36422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d267844 q = 1) : d36447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d36447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d36447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67944 (p : Pattern) (ha : d128239 p = 1) (hb : d267844 p = 1) : d269997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d267844 q = 1) : d36320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67925 q ha hb
    | true =>
      simp only [d16063, d36320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67923 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d267844 q = 1) : d36321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d36321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d267844 q = 1) : d36322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d36322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d267844 q = 1) : d36323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d36323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d267844 q = 1) : d36330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67926 q ha hb
    | true =>
      simp only [d16070, d36330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67924 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d267844 q = 1) : d36331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d36331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d267844 q = 1) : d36332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d36332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d267844 q = 1) : d36376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67935 q ha hb
    | true =>
      simp only [d16094, d36376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67918 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d267844 q = 1) : d269988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d269988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d267844 q = 1) : d36424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67936 q ha hb
    | true =>
      simp only [d16115, d36424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d267844 q = 1) : d36425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d36425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d267844 q = 1) : d269989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d269989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d267844 q = 1) : d269990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d269990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d267844 q = 1) : d269991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d269991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d267844 q = 1) : d36432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d36432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67940 q ha hb
    | true =>
      simp only [d16122, d36432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67938 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d267844 q = 1) : d36433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d36433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d36433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d267844 q = 1) : d36434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d36434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d36434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d267844 q = 1) : d36435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d36435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d36435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d267844 q = 1) : d36438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d36438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67941 q ha hb
    | true =>
      simp only [d16127, d36438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67939 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d267844 q = 1) : d36439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d36439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d36439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d267844 q = 1) : d36440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d36440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d36440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d267844 q = 1) : d36442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67942 q ha hb
    | true =>
      simp only [d16131, d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67920 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d267844 q = 1) : d269993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d267844 q = 1) : d36448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67943 q ha hb
    | true =>
      simp only [d16136, d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d267844 q = 1) : d36449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d267844 q = 1) : d269994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d267844 q = 1) : d269995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d269995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d267844 q = 1) : d269996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d269996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d267844 q = 1) : d269997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d269997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro67945 (p : Pattern) (ha : d128246 p = 1) (hb : d267844 p = 1) : d270004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d267844 q = 1) : d36442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67942 q ha hb
    | true =>
      simp only [d16131, d36442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67920 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d267844 q = 1) : d269993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d269993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d267844 q = 1) : d36448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67943 q ha hb
    | true =>
      simp only [d16136, d36448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d267844 q = 1) : d36449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d36449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d267844 q = 1) : d269994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d269994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d267844 q = 1) : d270002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d270002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d267844 q = 1) : d270003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d270003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d267844 q = 1) : d270004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d270004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d270004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67946 (p : Pattern) (ha : d16162 p = 1) (hb : d267844 p = 1) : d36495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d267844 q = 1) : d36481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d36481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67929 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d267844 q = 1) : d36341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67929 q ha hb
    | true =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d267844 q = 1) : d36482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d36482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d267844 q = 1) : d36342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d267844 q = 1) : d36483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d36483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d267844 q = 1) : d36484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d36484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d267844 q = 1) : d36485 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d36485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67930 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d267844 q = 1) : d36346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67930 q ha hb
    | true =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d267844 q = 1) : d36486 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d36486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d267844 q = 1) : d36347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d267844 q = 1) : d36487 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d36487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d267844 q = 1) : d36488 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d36488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d267844 q = 1) : d36489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d36489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d267844 q = 1) : d36490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d267844 q = 1) : d36491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d267844 q = 1) : d36492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d267844 q = 1) : d36493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d267844 q = 1) : d36219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d267844 q = 1) : d36220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d267844 q = 1) : d36221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d267844 q = 1) : d36222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16161 q = 1) (hb : d267844 q = 1) : d36494 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d36494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16161, d36494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16162 q = 1) (hb : d267844 q = 1) : d36495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d36495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16162, d36495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro67947 (p : Pattern) (ha : d16166 p = 1) (hb : d267844 p = 1) : d36499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d267844 q = 1) : d36219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d36219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d267844 q = 1) : d36127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67891 q ha hb
    | true =>
      simp only [d9382, d36127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d267844 q = 1) : d36220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d36220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d267844 q = 1) : d36128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d36128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d267844 q = 1) : d36221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d36221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d267844 q = 1) : d36222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d36222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d267844 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d267844 q = 1) : d36223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d36223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d267844 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d267844 q = 1) : d36499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d36499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d36499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67948 (p : Pattern) (ha : d16172 p = 1) (hb : d267844 p = 1) : d36505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d267844 q = 1) : d36496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d36496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67946 q ha hb
    | true =>
      simp only [d16163, d36496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67903 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d267844 q = 1) : d36497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d36497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d36497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d267844 q = 1) : d36498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d36498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d36498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d267844 q = 1) : d36500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d36500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67903 q ha hb
    | true =>
      simp only [d16167, d36500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67947 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d267844 q = 1) : d36501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d36501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d36501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d267844 q = 1) : d36502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d36502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d36502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d267844 q = 1) : d36503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d36503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d36503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d267844 q = 1) : d36225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67903 q ha hb
    | true =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d267844 q = 1) : d36226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d267844 q = 1) : d36227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d267844 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d267844 q = 1) : d36057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
    | true =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d267844 q = 1) : d36058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d267844 q = 1) : d36059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d267844 q = 1) : d36228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d267844 q = 1) : d36504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d36504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d36504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d267844 q = 1) : d36505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d36505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d36505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro67949 (p : Pattern) (ha : d16176 p = 1) (hb : d267844 p = 1) : d36510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d267844 q = 1) : d36225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67903 q ha hb
    | true =>
      simp only [d16005, d36225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d267844 q = 1) : d36226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d36226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d267844 q = 1) : d36227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d36227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d267844 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d267844 q = 1) : d36057 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67875 q ha hb
    | true =>
      simp only [d232, d36057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d267844 q = 1) : d36058 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d36058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d267844 q = 1) : d36059 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d36059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d267844 q = 1) : d36228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d36228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d267844 q = 1) : d36508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d36508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d267844 q = 1) : d36509 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d36509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d36509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d267844 q = 1) : d36510 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d36510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d36510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro67950 (p : Pattern) (ha : d16182 p = 1) (hb : d267844 p = 1) : d36516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d267844 q = 1) : d36506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d36506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67948 q ha hb
    | true =>
      simp only [d16173, d36506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d267844 q = 1) : d36507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d36507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d36507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d267844 q = 1) : d36511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67949 q ha hb
    | true =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d267844 q = 1) : d36512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d267844 q = 1) : d36513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d36513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d36513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d267844 q = 1) : d36514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d36514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d36514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d267844 q = 1) : d36515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d36515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d36515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d267844 q = 1) : d36516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d36516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d36516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67951 (p : Pattern) (ha : d16186 p = 1) (hb : d267844 p = 1) : d36524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d267844 q = 1) : d36511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67949 q ha hb
    | true =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d267844 q = 1) : d36512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d267844 q = 1) : d36519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67914 q ha hb
    | true =>
      simp only [d684, d36519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d267844 q = 1) : d36520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d36520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d267844 q = 1) : d36521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d36521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d36521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d267844 q = 1) : d36522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d36522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d36522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d267844 q = 1) : d36523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d36523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d36523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d267844 q = 1) : d36524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d36524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d36524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67952 (p : Pattern) (ha : d16207 p = 1) (hb : d267844 p = 1) : d36563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d267844 q = 1) : d36511 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67949 q ha hb
    | true =>
      simp only [d16177, d36511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d267844 q = 1) : d36512 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d36512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d267844 q = 1) : d36560 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d36560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d36560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d267844 q = 1) : d36561 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d36561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d36561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d267844 q = 1) : d36562 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d36562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d36562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d267844 q = 1) : d36563 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d36563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d36563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67953 (p : Pattern) (ha : d128256 p = 1) (hb : d267844 p = 1) : d270014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d267844 q = 1) : d36525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d36525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67950 q ha hb
    | true =>
      simp only [d16187, d36525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67951 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d267844 q = 1) : d270010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d270010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d270010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d267844 q = 1) : d36564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d36564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67952 q ha hb
    | true =>
      simp only [d16208, d36564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d267844 q = 1) : d36565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d36565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d36565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d267844 q = 1) : d270011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d270011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d270011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d267844 q = 1) : d270012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d270012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d270012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d267844 q = 1) : d270013 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d270013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d270013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d267844 q = 1) : d270014 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d270014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d270014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67954 (p : Pattern) (ha : d128262 p = 1) (hb : d267844 p = 1) : d270020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d267844 q = 1) : d36303 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d36303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d36303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67919 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d267844 q = 1) : d36304 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d36304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d36304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d267844 q = 1) : d36313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67919 q ha hb
    | true =>
      simp only [d16058, d36313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67921 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d267844 q = 1) : d36314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d36314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d267844 q = 1) : d36315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d36315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d36315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d267844 q = 1) : d269998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67937 q ha hb
    | true =>
      simp only [d128240, d269998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67944 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d267844 q = 1) : d36467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d36467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67922 q ha hb
    | true =>
      simp only [d16144, d36467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67912 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d267844 q = 1) : d269999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d269999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d267844 q = 1) : d270000 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d270000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d270000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d267844 q = 1) : d270001 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d270001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d270001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d267844 q = 1) : d270005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d270005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d270005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67945 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d267844 q = 1) : d36476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d36476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d36476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67913 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d267844 q = 1) : d270006 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d270006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d270006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d267844 q = 1) : d270007 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d270007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d270007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d267844 q = 1) : d270008 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d270008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d270008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d267844 q = 1) : d270009 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d270009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d270009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d267844 q = 1) : d270015 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d270015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d270015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67953 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d267844 q = 1) : d36581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d36581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d36581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67916 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d267844 q = 1) : d270016 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d270016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d270016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d267844 q = 1) : d270017 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d270017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d270017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d267844 q = 1) : d270018 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d270018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d270018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d267844 q = 1) : d270019 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d270019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d270019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d267844 q = 1) : d270020 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d270020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d270020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67955 (p : Pattern) (ha : d128268 p = 1) (hb : d267844 p = 1) : d270026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d267844 q = 1) : d270021 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d270021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d270021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67954 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d267844 q = 1) : d270022 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d270022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d270022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d267844 q = 1) : d270023 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d270023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d270023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d267844 q = 1) : d270024 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d270024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d270024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d267844 q = 1) : d270025 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d270025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d270025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d267844 q = 1) : d270026 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d270026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d270026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67956 (p : Pattern) (ha : d750 p = 1) (hb : d267844 p = 1) : d36594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d267844 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d267844 q = 1) : d9454 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d9454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d267844 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d267844 q = 1) : d36005 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d36005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d267844 q = 1) : d36006 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d36006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d750 q = 1) (hb : d267844 q = 1) : d36594 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d36594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d750, d36594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro67957 (p : Pattern) (ha : d758 p = 1) (hb : d267844 p = 1) : d36603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d267844 q = 1) : d36121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
    | true =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d267844 q = 1) : d36122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d267844 q = 1) : d36123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d36123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d267844 q = 1) : d36124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d36124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d267844 q = 1) : d36597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d267844 q = 1) : d36598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d267844 q = 1) : d36601 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d36601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d36601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d267844 q = 1) : d36602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d267844 q = 1) : d36603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d36603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d36603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67958 (p : Pattern) (ha : d762 p = 1) (hb : d267844 p = 1) : d36607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d267844 q = 1) : d36597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d267844 q = 1) : d36598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d267844 q = 1) : d36602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d267844 q = 1) : d36607 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d36607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d36607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67959 (p : Pattern) (ha : d773 p = 1) (hb : d267844 p = 1) : d36618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d267844 q = 1) : d36608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67957 q ha hb
    | true =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67958 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d267844 q = 1) : d36609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d267844 q = 1) : d36610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d267844 q = 1) : d36612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d267844 q = 1) : d36617 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d36617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d36617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d267844 q = 1) : d36618 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d36618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d36618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67960 (p : Pattern) (ha : d783 p = 1) (hb : d267844 p = 1) : d36628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d267844 q = 1) : d36626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d267844 q = 1) : d36627 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d267844 q = 1) : d36628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d36628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d36628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67961 (p : Pattern) (ha : d793 p = 1) (hb : d267844 p = 1) : d36638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d267844 q = 1) : d36626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d267844 q = 1) : d36627 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d36627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d267844 q = 1) : d36638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d36638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d36638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67962 (p : Pattern) (ha : d950 p = 1) (hb : d267844 p = 1) : d36817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d267844 q = 1) : d36806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67960 q ha hb
    | true =>
      simp only [d939, d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d267844 q = 1) : d36807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d267844 q = 1) : d36808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d267844 q = 1) : d36809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d267844 q = 1) : d36810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d267844 q = 1) : d36812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67961 q ha hb
    | true =>
      simp only [d945, d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d267844 q = 1) : d36813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d267844 q = 1) : d36814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d267844 q = 1) : d36815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d267844 q = 1) : d36816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d267844 q = 1) : d36817 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d36817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d36817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67963 (p : Pattern) (ha : d959 p = 1) (hb : d267844 p = 1) : d36826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d267844 q = 1) : d36812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67961 q ha hb
    | true =>
      simp only [d945, d36812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d267844 q = 1) : d36813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d36813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d267844 q = 1) : d36814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d36814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d267844 q = 1) : d36815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d36815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d267844 q = 1) : d36816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d36816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d267844 q = 1) : d36826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d36826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d36826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67964 (p : Pattern) (ha : d981 p = 1) (hb : d267844 p = 1) : d36863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d267844 q = 1) : d36214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d36214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d267844 q = 1) : d36121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67890 q ha hb
    | true =>
      simp only [d319, d36121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d267844 q = 1) : d36215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d36215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d267844 q = 1) : d36122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d36122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d267844 q = 1) : d36216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d36216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d267844 q = 1) : d36217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d36217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d267844 q = 1) : d36847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d267844 q = 1) : d36848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d267844 q = 1) : d36849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d267844 q = 1) : d36850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d267844 q = 1) : d36862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d36862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d36862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d267844 q = 1) : d36856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d267844 q = 1) : d36863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d36863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d36863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67965 (p : Pattern) (ha : d986 p = 1) (hb : d267844 p = 1) : d36867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d267844 q = 1) : d36847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d36847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d267844 q = 1) : d36848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d36848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d267844 q = 1) : d36849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d36849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d267844 q = 1) : d36850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d36850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d267844 q = 1) : d36856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d36856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d267844 q = 1) : d36867 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d36867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d36867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67966 (p : Pattern) (ha : d1005 p = 1) (hb : d267844 p = 1) : d36886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d267844 q = 1) : d36868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d36868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67964 q ha hb
    | true =>
      simp only [d987, d36868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67965 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d267844 q = 1) : d36869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d36869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d36869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d267844 q = 1) : d36870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d36870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d36870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d267844 q = 1) : d36876 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d36876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d36876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d267844 q = 1) : d36885 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d36885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d36885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d267844 q = 1) : d36886 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d36886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d36886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67967 (p : Pattern) (ha : d1063 p = 1) (hb : d267844 p = 1) : d36957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d267844 q = 1) : d36887 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d36887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67966 q ha hb
    | true =>
      simp only [d1006, d36887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d267844 q = 1) : d36888 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d36888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d36888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d267844 q = 1) : d36954 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d36954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d36954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d267844 q = 1) : d36955 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d36955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d36955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d267844 q = 1) : d36956 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d36956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d36956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d267844 q = 1) : d36957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d36957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d36957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67968 (p : Pattern) (ha : d1069 p = 1) (hb : d267844 p = 1) : d36963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d267844 q = 1) : d36958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d36958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67967 q ha hb
    | true =>
      simp only [d1064, d36958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d267844 q = 1) : d36959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d36959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d36959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d267844 q = 1) : d36960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d36960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d36960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d267844 q = 1) : d36961 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d36961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d36961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d267844 q = 1) : d36962 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d36962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d36962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d267844 q = 1) : d36963 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d36963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d36963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67969 (p : Pattern) (ha : d16227 p = 1) (hb : d267844 p = 1) : d36600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d267844 q = 1) : d36341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67929 q ha hb
    | true =>
      simp only [d543, d36341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d267844 q = 1) : d36342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d36342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d267844 q = 1) : d36343 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d36343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d267844 q = 1) : d36344 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d36344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d267844 q = 1) : d36346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67930 q ha hb
    | true =>
      simp only [d9458, d36346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d267844 q = 1) : d36347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d36347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d267844 q = 1) : d36348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d36348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d267844 q = 1) : d36349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d36349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d267844 q = 1) : d36350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d36350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d267844 q = 1) : d36356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d267844 q = 1) : d36357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d267844 q = 1) : d36597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d267844 q = 1) : d36598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12750 q = 1) (hb : d267844 q = 1) : d36599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12750, d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16227 q = 1) (hb : d267844 q = 1) : d36600 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d36600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16227, d36600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67970 (p : Pattern) (ha : d16233 p = 1) (hb : d267844 p = 1) : d36614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d267844 q = 1) : d36604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67969 q ha hb
    | true =>
      simp only [d16228, d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67957 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d267844 q = 1) : d36605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d267844 q = 1) : d36606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d267844 q = 1) : d36608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67957 q ha hb
    | true =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67958 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d267844 q = 1) : d36609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d267844 q = 1) : d36610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d267844 q = 1) : d36611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d267844 q = 1) : d36612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d36612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d267844 q = 1) : d36613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d36613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d36613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16233 q = 1) (hb : d267844 q = 1) : d36614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d36614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16233, d36614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro67971 (p : Pattern) (ha : d16239 p = 1) (hb : d267844 p = 1) : d36624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d267844 q = 1) : d36622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d267844 q = 1) : d36623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d267844 q = 1) : d36624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d36624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d36624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67972 (p : Pattern) (ha : d16245 p = 1) (hb : d267844 p = 1) : d36634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d267844 q = 1) : d36629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67971 q ha hb
    | true =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67960 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d267844 q = 1) : d36630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d267844 q = 1) : d36631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d267844 q = 1) : d36632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d267844 q = 1) : d36633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d267844 q = 1) : d36634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d36634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d36634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67973 (p : Pattern) (ha : d16248 p = 1) (hb : d267844 p = 1) : d36637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d267844 q = 1) : d36622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d267844 q = 1) : d36623 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d36623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d267844 q = 1) : d36637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d36637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d36637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67974 (p : Pattern) (ha : d16254 p = 1) (hb : d267844 p = 1) : d36644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d267844 q = 1) : d36629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67971 q ha hb
    | true =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67960 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d267844 q = 1) : d36630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d267844 q = 1) : d36631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d267844 q = 1) : d36632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d267844 q = 1) : d36633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d267844 q = 1) : d36639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67973 q ha hb
    | true =>
      simp only [d16249, d36639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67961 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d267844 q = 1) : d36640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d36640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d267844 q = 1) : d36641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d36641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d267844 q = 1) : d36642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d36642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d267844 q = 1) : d36643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d36643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d267844 q = 1) : d36644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d36644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d36644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67975 (p : Pattern) (ha : d16343 p = 1) (hb : d267844 p = 1) : d36811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d267844 q = 1) : d36629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67971 q ha hb
    | true =>
      simp only [d16240, d36629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67960 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d267844 q = 1) : d36630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d36630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d267844 q = 1) : d36631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d36631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d267844 q = 1) : d36632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d36632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d267844 q = 1) : d36633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d36633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d267844 q = 1) : d36806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67960 q ha hb
    | true =>
      simp only [d939, d36806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d267844 q = 1) : d36807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d36807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d267844 q = 1) : d36808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d36808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d267844 q = 1) : d36809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d36809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d267844 q = 1) : d36810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d36810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d267844 q = 1) : d36811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d36811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d36811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67976 (p : Pattern) (ha : d806 p = 1) (hb : d267844 p = 1) : d36651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d267844 q = 1) : d36626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d267844 q = 1) : d36650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d267844 q = 1) : d36651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d36651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d36651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67977 (p : Pattern) (ha : d816 p = 1) (hb : d267844 p = 1) : d36661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d267844 q = 1) : d36659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d267844 q = 1) : d36660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d267844 q = 1) : d36661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d36661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d36661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67978 (p : Pattern) (ha : d16259 p = 1) (hb : d267844 p = 1) : d36649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d267844 q = 1) : d36622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d267844 q = 1) : d36648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d267844 q = 1) : d36649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d36649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d36649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67979 (p : Pattern) (ha : d16266 p = 1) (hb : d267844 p = 1) : d36658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d267844 q = 1) : d36656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d267844 q = 1) : d36657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d267844 q = 1) : d36658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d36658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d36658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67980 (p : Pattern) (ha : d821 p = 1) (hb : d216468 p = 1) : d36665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d820 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d529 q = 1) (hb : d216468 q = 1) : d36333 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d529, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d821 q = 1) (hb : d216468 q = 1) : d36665 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d821, d36665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d821, d36665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67981 (p : Pattern) (ha : d827 p = 1) (hb : d216468 p = 1) : d36334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d825 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d826 q = 1) (hb : d216468 q = 1) : d36333 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d826, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d826, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d534 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d535 q = 1) (hb : d216468 q = 1) : d36113 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d535, d36113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d827 q = 1) (hb : d216468 q = 1) : d36334 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d827, d36334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d827, d36334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67982 (p : Pattern) (ha : d833 p = 1) (hb : d267844 p = 1) : d36671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d216468 q = 1) : d36666 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d36666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67980 q ha hb
    | true =>
      simp only [d822, d36666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d267844 q = 1) : d36667 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d267844, d36667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d267844, d36667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d216468 q = 1) : d36335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67927 q ha hb
    | true =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d267844 q = 1) : d36336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d267844 q = 1) : d36668 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d36668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d36668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d828 q = 1) (hb : d216468 q = 1) : d36335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67981 q ha hb
    | true =>
      simp only [d828, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d829 q = 1) (hb : d267844 q = 1) : d36336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d829, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d537 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67928 q ha hb
    | true =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d538 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d830 q = 1) (hb : d267844 q = 1) : d36337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d830, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d831 q = 1) (hb : d267844 q = 1) : d36669 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d36669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d831, d36669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d832 q = 1) (hb : d267844 q = 1) : d36670 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d36670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d832, d36670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d533 q = 1) (hb : d267844 q = 1) : d36337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d539 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d540 q = 1) (hb : d267844 q = 1) : d36338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d541 q = 1) (hb : d267844 q = 1) : d36339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h23 (q : Pattern) (ha : d833 q = 1) (hb : d267844 q = 1) : d36671 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d36671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d833, d36671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67983 (p : Pattern) (ha : d9586 p = 1) (hb : d267844 p = 1) : d36676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d216468 q = 1) : d36335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67927 q ha hb
    | true =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d267844 q = 1) : d36336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67889 q ha hb
    | true =>
      simp only [d313, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d267844 q = 1) : d36337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d36337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d537 q = 1) (hb : d216468 q = 1) : d36115 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67928 q ha hb
    | true =>
      simp only [d537, d36115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d538 q = 1) (hb : d267844 q = 1) : d36116 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d538, d267844, d36116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d216468 q = 1) : d9452 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67869 q ha hb
    | true =>
      simp only [d133, d9452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d267844 q = 1) : d9453 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d267844, d9453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d539 q = 1) (hb : d267844 q = 1) : d36117 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d539, d36117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d540 q = 1) (hb : d267844 q = 1) : d36338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d540, d36338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d541 q = 1) (hb : d267844 q = 1) : d36339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d541, d36339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9585 q = 1) (hb : d267844 q = 1) : d9585 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9586 q = 1) (hb : d267844 q = 1) : d36676 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9586, d36676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9586, d36676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67984 (p : Pattern) (ha : d9596 p = 1) (hb : d267844 p = 1) : d36685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d216468 q = 1) : d36335 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67927 q ha hb
    | true =>
      simp only [d531, d36335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d267844 q = 1) : d36336 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d267844, d36336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d267844 q = 1) : d9582 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9593 q = 1) (hb : d267844 q = 1) : d36682 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d36682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9593, d36682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9594 q = 1) (hb : d267844 q = 1) : d36683 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d36683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9594, d36683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9595 q = 1) (hb : d267844 q = 1) : d36684 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d36684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9595, d36684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d9585 q = 1) (hb : d267844 q = 1) : d9585 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9596 q = 1) (hb : d267844 q = 1) : d36685 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9596, d36685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9596, d36685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67985 (p : Pattern) (ha : d16274 p = 1) (hb : d267844 p = 1) : d36691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d267844 q = 1) : d36672 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67982 q ha hb
    | true =>
      simp only [d834, d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d267844 q = 1) : d36673 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d267844 q = 1) : d36674 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d36674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d36674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d267844 q = 1) : d36675 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d36675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d36675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9587 q = 1) (hb : d267844 q = 1) : d36677 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67983 q ha hb
    | true =>
      simp only [d9587, d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d267844 q = 1) : d36678 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9589, d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16270 q = 1) (hb : d267844 q = 1) : d36679 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d36679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d36679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16271 q = 1) (hb : d267844 q = 1) : d36680 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d36680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16271, d36680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16272 q = 1) (hb : d267844 q = 1) : d36681 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d36681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, d36681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9597 q = 1) (hb : d267844 q = 1) : d36686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67984 q ha hb
    | true =>
      simp only [d9597, d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d267844 q = 1) : d36687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9599, d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14529 q = 1) (hb : d267844 q = 1) : d36688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d36688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d36688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14530 q = 1) (hb : d267844 q = 1) : d36689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d36689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14530, d36689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12748 q = 1) (hb : d267844 q = 1) : d36356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12749 q = 1) (hb : d267844 q = 1) : d36357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16273 q = 1) (hb : d267844 q = 1) : d36690 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d36690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16273, d36690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16274 q = 1) (hb : d267844 q = 1) : d36691 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d36691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16274, d36691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67986 (p : Pattern) (ha : d16278 p = 1) (hb : d267844 p = 1) : d36695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d267844 q = 1) : d36356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d36356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d267844 q = 1) : d36357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d36357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d267844 q = 1) : d36595 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67956 q ha hb
    | true =>
      simp only [d751, d36595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d267844 q = 1) : d36596 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d36596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d267844 q = 1) : d36597 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d36597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d267844 q = 1) : d36598 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d36598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d267844 q = 1) : d36599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d36599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d267844 q = 1) : d36602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d36602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16278 q = 1) (hb : d267844 q = 1) : d36695 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d36695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16278, d36695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67987 (p : Pattern) (ha : d16284 p = 1) (hb : d267844 p = 1) : d36701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d267844 q = 1) : d36692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d36692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67985 q ha hb
    | true =>
      simp only [d16275, d36692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67969 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d267844 q = 1) : d36693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d36693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d36693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d267844 q = 1) : d36694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d36694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d36694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d267844 q = 1) : d36696 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d36696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67969 q ha hb
    | true =>
      simp only [d16279, d36696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67986 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d267844 q = 1) : d36697 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d36697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d36697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d267844 q = 1) : d36698 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d36698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d36698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d267844 q = 1) : d36699 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d36699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d36699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d267844 q = 1) : d36604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67969 q ha hb
    | true =>
      simp only [d16228, d36604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67957 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d267844 q = 1) : d36605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d36605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d267844 q = 1) : d36606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d36606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d267844 q = 1) : d36608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67957 q ha hb
    | true =>
      simp only [d763, d36608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67958 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d267844 q = 1) : d36609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d36609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d267844 q = 1) : d36610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d36610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d267844 q = 1) : d36611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d36611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d267844 q = 1) : d36700 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d36700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d36700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16284 q = 1) (hb : d267844 q = 1) : d36701 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d36701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16284, d36701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro67988 (p : Pattern) (ha : d16290 p = 1) (hb : d267844 p = 1) : d36707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d267844 q = 1) : d36702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67987 q ha hb
    | true =>
      simp only [d16285, d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d267844 q = 1) : d36703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d267844 q = 1) : d36704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d267844 q = 1) : d36705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d267844 q = 1) : d36706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d267844 q = 1) : d36707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d36707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d36707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67989 (p : Pattern) (ha : d16314 p = 1) (hb : d267844 p = 1) : d36774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d267844 q = 1) : d36771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d267844 q = 1) : d36772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d267844 q = 1) : d36773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d267844 q = 1) : d36774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d36774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d36774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67990 (p : Pattern) (ha : d128274 p = 1) (hb : d267844 p = 1) : d270032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d267844 q = 1) : d36652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67978 q ha hb
    | true =>
      simp only [d16260, d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67976 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d267844 q = 1) : d36653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d267844 q = 1) : d36654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d267844 q = 1) : d36655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d267844 q = 1) : d36662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67979 q ha hb
    | true =>
      simp only [d16267, d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67977 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d267844 q = 1) : d36663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d267844 q = 1) : d36664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d267844 q = 1) : d36708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67988 q ha hb
    | true =>
      simp only [d16291, d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67971 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d267844 q = 1) : d270028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d267844 q = 1) : d36775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67989 q ha hb
    | true =>
      simp only [d16315, d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d267844 q = 1) : d36776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d267844 q = 1) : d270029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d267844 q = 1) : d270030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d267844 q = 1) : d270031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d267844 q = 1) : d270032 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d270032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67991 (p : Pattern) (ha : d916 p = 1) (hb : d267844 p = 1) : d36782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d267844 q = 1) : d36626 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d36626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d267844 q = 1) : d36650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d36650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d267844 q = 1) : d36782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d36782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d36782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67992 (p : Pattern) (ha : d922 p = 1) (hb : d267844 p = 1) : d36788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d267844 q = 1) : d36625 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d36625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d267844 q = 1) : d36659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d36659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d267844 q = 1) : d36660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d36660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d267844 q = 1) : d36788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d36788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d36788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67993 (p : Pattern) (ha : d16321 p = 1) (hb : d267844 p = 1) : d36781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d267844 q = 1) : d36622 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d36622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d267844 q = 1) : d36648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d36648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d267844 q = 1) : d36781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d36781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d36781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67994 (p : Pattern) (ha : d16326 p = 1) (hb : d267844 p = 1) : d36787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d267844 q = 1) : d36619 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67959 q ha hb
    | true =>
      simp only [d774, d36619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d267844 q = 1) : d36620 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d36620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d267844 q = 1) : d36621 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d36621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d267844 q = 1) : d36656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d36656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d267844 q = 1) : d36657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d36657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d267844 q = 1) : d36787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d36787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d36787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67995 (p : Pattern) (ha : d16330 p = 1) (hb : d267844 p = 1) : d36792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d267844 q = 1) : d36702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67987 q ha hb
    | true =>
      simp only [d16285, d36702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d267844 q = 1) : d36703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d36703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d267844 q = 1) : d36704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d36704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d267844 q = 1) : d36705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d36705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d267844 q = 1) : d36706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d36706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d267844 q = 1) : d36792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d36792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d36792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro67996 (p : Pattern) (ha : d16335 p = 1) (hb : d267844 p = 1) : d36798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d267844 q = 1) : d36615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67970 q ha hb
    | true =>
      simp only [d16234, d36615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d267844 q = 1) : d36616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d36616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d267844 q = 1) : d36771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d36771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d267844 q = 1) : d36772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d36772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d267844 q = 1) : d36773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d36773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d267844 q = 1) : d36798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d36798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d36798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67997 (p : Pattern) (ha : d128279 p = 1) (hb : d267844 p = 1) : d270037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d267844 q = 1) : d36652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67978 q ha hb
    | true =>
      simp only [d16260, d36652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67976 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d267844 q = 1) : d36653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d36653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d267844 q = 1) : d36654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d36654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d267844 q = 1) : d36655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d36655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d267844 q = 1) : d36662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67979 q ha hb
    | true =>
      simp only [d16267, d36662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67977 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d267844 q = 1) : d36663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d36663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d267844 q = 1) : d36664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d36664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d267844 q = 1) : d36708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67988 q ha hb
    | true =>
      simp only [d16291, d36708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67971 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d267844 q = 1) : d270028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d270028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d267844 q = 1) : d36775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67989 q ha hb
    | true =>
      simp only [d16315, d36775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d267844 q = 1) : d36776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d36776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d267844 q = 1) : d270029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d270029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d267844 q = 1) : d270030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d270030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d267844 q = 1) : d270031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d270031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d267844 q = 1) : d36783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d36783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67993 q ha hb
    | true =>
      simp only [d16322, d36783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67991 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d267844 q = 1) : d36784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d36784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d36784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d267844 q = 1) : d36785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d36785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d36785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d267844 q = 1) : d36786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d36786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d36786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d267844 q = 1) : d36789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d36789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67994 q ha hb
    | true =>
      simp only [d16327, d36789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67992 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d267844 q = 1) : d36790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d36790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d36790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d267844 q = 1) : d36791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d36791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d36791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d267844 q = 1) : d36793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67995 q ha hb
    | true =>
      simp only [d16331, d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67973 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d267844 q = 1) : d270033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d267844 q = 1) : d36799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67996 q ha hb
    | true =>
      simp only [d16336, d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d267844 q = 1) : d36800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d267844 q = 1) : d270034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d267844 q = 1) : d270035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d270035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d267844 q = 1) : d270036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d270036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d267844 q = 1) : d270037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d270037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro67998 (p : Pattern) (ha : d128286 p = 1) (hb : d267844 p = 1) : d270044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d267844 q = 1) : d36793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67995 q ha hb
    | true =>
      simp only [d16331, d36793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67973 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d267844 q = 1) : d270033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d270033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d267844 q = 1) : d36799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67996 q ha hb
    | true =>
      simp only [d16336, d36799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d267844 q = 1) : d36800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d36800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d267844 q = 1) : d270034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d270034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d267844 q = 1) : d270042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d270042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d267844 q = 1) : d270043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d270043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d267844 q = 1) : d270044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d270044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d270044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67999 (p : Pattern) (ha : d16362 p = 1) (hb : d267844 p = 1) : d36846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d267844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d267844 q = 1) : d36832 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d36832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d36832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67982 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d267844 q = 1) : d36672 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67982 q ha hb
    | true =>
      simp only [d834, d36672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d267844 q = 1) : d36833 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d36833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d36833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d267844 q = 1) : d36673 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d36673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d267844 q = 1) : d36834 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d36834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d36834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d267844 q = 1) : d36835 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d36835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d36835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d267844 q = 1) : d36836 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d36836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d36836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67983 q ha hb
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d267844 q = 1) : d36677 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67983 q ha hb
    | true =>
      simp only [d9587, d36677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d267844 q = 1) : d36837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d36837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16357, d36837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9589 q = 1) (hb : d267844 q = 1) : d36678 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9589, d36678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16358 q = 1) (hb : d267844 q = 1) : d36838 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d36838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16358, d36838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16359 q = 1) (hb : d267844 q = 1) : d36839 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d36839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16359, d36839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16360 q = 1) (hb : d267844 q = 1) : d36840 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d36840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16360, d36840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d267844 q = 1) : d36841 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d36841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d36841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67984 q ha hb
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d267844 q = 1) : d36686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67984 q ha hb
    | true =>
      simp only [d9597, d36686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14645 q = 1) (hb : d267844 q = 1) : d36842 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d36842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14645, d36842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9599 q = 1) (hb : d267844 q = 1) : d36687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9599, d36687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14646 q = 1) (hb : d267844 q = 1) : d36843 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d36843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14646, d36843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14647 q = 1) (hb : d267844 q = 1) : d36844 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d36844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14647, d36844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d267844 q = 1) : d36490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d36490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d267844 q = 1) : d36354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67931 q ha hb
    | true =>
      simp only [d9468, d36354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12859 q = 1) (hb : d267844 q = 1) : d36491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12859, d36491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9470 q = 1) (hb : d267844 q = 1) : d36355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9470, d36355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12860 q = 1) (hb : d267844 q = 1) : d36492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12860, d36492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12861 q = 1) (hb : d267844 q = 1) : d36493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12861, d36493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16361 q = 1) (hb : d267844 q = 1) : d36845 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d36845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16361, d36845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16362 q = 1) (hb : d267844 q = 1) : d36846 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d36846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16362, d36846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
end NetHack.Soko22Hazard87
