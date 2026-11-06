import NetHack.Soko22Hazard87.EqIntroBlocks0139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro35000 (p : Pattern) (selected : d334834 p = 0) : d336534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334825 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34998 q selected
    | true =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334826 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334831 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334831, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334831, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334832 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334832, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334832, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334833 q = 0) : d336533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334833, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334833, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334834 q = 0) : d336534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334834, d336534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334834, d336534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35001 (p : Pattern) (selected : d334839 p = 0) : d336591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334646 q = 0) : d336475 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334646, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334646, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334647 q = 0) : d336476 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334647, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334647, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334658 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334837 q = 0) : d336589 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334837, d336589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334837, d336589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334838 q = 0) : d336590 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334838, d336590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334838, d336590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334839 q = 0) : d336591 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334839, d336591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334839, d336591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35002 (p : Pattern) (selected : d334845 p = 0) : d336597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334662 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
    | true =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334663 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334664 q = 0) : d336493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334664, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334664, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334665 q = 0) : d336494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334665, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334665, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334669 q = 0) : d336498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334670 q = 0) : d336499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334671 q = 0) : d336500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334671, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334671, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334840 q = 0) : d336592 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334840, d336592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35001 q selected
    | true =>
      simp only [d334840, d336592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334841 q = 0) : d336593 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334841, d336593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334841, d336593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334842 q = 0) : d336594 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334842, d336594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334842, d336594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334843 q = 0) : d336595 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334843, d336595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334843, d336595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334844 q = 0) : d336596 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334844, d336596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334844, d336596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334845 q = 0) : d336597 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334845, d336597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334845, d336597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35003 (p : Pattern) (selected : d334846 p = 0) : d336598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334658 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334659 q = 0) : d336488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334660 q = 0) : d336489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334837 q = 0) : d336589 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334837, d336589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334837, d336589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334838 q = 0) : d336590 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334838, d336590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334838, d336590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334846 q = 0) : d336598 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334846, d336598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334846, d336598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35004 (p : Pattern) (selected : d334852 p = 0) : d336604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334847 q = 0) : d336599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334847, d336599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35003 q selected
    | true =>
      simp only [d334847, d336599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334848 q = 0) : d336600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334848, d336600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334848, d336600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334849 q = 0) : d336601 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334849, d336601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334849, d336601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334850 q = 0) : d336602 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334850, d336602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334850, d336602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334851 q = 0) : d336603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334851, d336603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334851, d336603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334852 q = 0) : d336604 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334852, d336604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334852, d336604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35005 (p : Pattern) (selected : d334858 p = 0) : d336610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334674 q = 0) : d336503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34967 q selected
    | true =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
  have h2 (q : Pattern) (selected : d334675 q = 0) : d336504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334676 q = 0) : d336505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334685 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
    | true =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34972 q selected
  have h5 (q : Pattern) (selected : d334686 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334687 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334688 q = 0) : d336517 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334853 q = 0) : d336605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334853, d336605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35002 q selected
    | true =>
      simp only [d334853, d336605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35004 q selected
  have h9 (q : Pattern) (selected : d334854 q = 0) : d336606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334854, d336606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334854, d336606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334855 q = 0) : d336607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334855, d336607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334855, d336607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334856 q = 0) : d336608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334856, d336608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334856, d336608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334857 q = 0) : d336609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334857, d336609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334857, d336609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334858 q = 0) : d336610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334858, d336610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334858, d336610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro35006 (p : Pattern) (selected : d334864 p = 0) : d336616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334859 q = 0) : d336611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334859, d336611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35005 q selected
    | true =>
      simp only [d334859, d336611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334860 q = 0) : d336612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334860, d336612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334860, d336612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334861 q = 0) : d336613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334861, d336613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334861, d336613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334862 q = 0) : d336614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334862, d336614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334862, d336614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334863 q = 0) : d336615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334863, d336615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334863, d336615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334864 q = 0) : d336616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334864, d336616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334864, d336616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35007 (p : Pattern) (selected : d334870 p = 0) : d336622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334729 q = 0) : d336558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334729, d336558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34981 q selected
    | true =>
      simp only [d334729, d336558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34982 q selected
  have h2 (q : Pattern) (selected : d334730 q = 0) : d336559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334730, d336559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334730, d336559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334731 q = 0) : d336560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334731, d336560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334731, d336560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334732 q = 0) : d336561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334732, d336561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334732, d336561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334739 q = 0) : d336568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334739, d336568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34983 q selected
    | true =>
      simp only [d334739, d336568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34984 q selected
  have h6 (q : Pattern) (selected : d334740 q = 0) : d336569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334740, d336569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334740, d336569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334741 q = 0) : d336570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334741, d336570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334741, d336570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334758 q = 0) : d336587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334758, d336587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34987 q selected
    | true =>
      simp only [d334758, d336587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34975 q selected
  have h9 (q : Pattern) (selected : d334835 q = 0) : d336535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334835, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34999 q selected
    | true =>
      simp only [d334835, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35000 q selected
  have h10 (q : Pattern) (selected : d334836 q = 0) : d336588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334836, d336588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334836, d336588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334865 q = 0) : d336617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334865, d336617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35006 q selected
    | true =>
      simp only [d334865, d336617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334866 q = 0) : d336618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334866, d336618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334866, d336618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334867 q = 0) : d336619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334867, d336619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334867, d336619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334868 q = 0) : d336620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334868, d336620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334868, d336620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334869 q = 0) : d336621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334869, d336621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334869, d336621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334870 q = 0) : d336622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334870, d336622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334870, d336622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro35008 (p : Pattern) (selected : d334871 p = 0) : d336623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334699 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334725 q = 0) : d336554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334725, d336554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334725, d336554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334871 q = 0) : d336623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334871, d336623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334871, d336623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35009 (p : Pattern) (selected : d334872 p = 0) : d336624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334703 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334727 q = 0) : d336556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334727, d336556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334727, d336556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334872 q = 0) : d336624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334872, d336624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334872, d336624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35010 (p : Pattern) (selected : d334877 p = 0) : d336629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334733 q = 0) : d336562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334733, d336562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334733, d336562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334734 q = 0) : d336563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334734, d336563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334734, d336563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334877 q = 0) : d336629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334877, d336629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334877, d336629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35011 (p : Pattern) (selected : d334878 p = 0) : d336630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334736 q = 0) : d336565 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334736, d336565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334736, d336565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334737 q = 0) : d336566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334737, d336566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334737, d336566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334878 q = 0) : d336630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334878, d336630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334878, d336630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35012 (p : Pattern) (selected : d334882 p = 0) : d336634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334752 q = 0) : d336581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334752, d336581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34986 q selected
    | true =>
      simp only [d334752, d336581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334753 q = 0) : d336582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334753, d336582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334753, d336582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334754 q = 0) : d336583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334754, d336583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334754, d336583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334755 q = 0) : d336584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334755, d336584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334755, d336584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334756 q = 0) : d336585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334756, d336585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334756, d336585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334882 q = 0) : d336634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334882, d336634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334882, d336634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35013 (p : Pattern) (selected : d334884 p = 0) : d336543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334821 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334821, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34997 q selected
    | true =>
      simp only [d334821, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334822 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334822, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334822, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334825 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34998 q selected
    | true =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334826 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334827 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334827, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334827, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334828 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334828, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334828, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334829 q = 0) : d336529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334829, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334829, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334884 q = 0) : d336543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334884, d336543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334884, d336543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35014 (p : Pattern) (selected : d334885 p = 0) : d336544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334825 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34998 q selected
    | true =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334826 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334831 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334831, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334831, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334832 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334832, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334832, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334833 q = 0) : d336533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334833, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334833, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334885 q = 0) : d336544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334885, d336544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334885, d336544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35015 (p : Pattern) (selected : d334888 p = 0) : d336637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334859 q = 0) : d336611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334859, d336611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35005 q selected
    | true =>
      simp only [d334859, d336611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334860 q = 0) : d336612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334860, d336612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334860, d336612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334861 q = 0) : d336613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334861, d336613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334861, d336613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334862 q = 0) : d336614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334862, d336614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334862, d336614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334863 q = 0) : d336615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334863, d336615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334863, d336615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334888 q = 0) : d336637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334888, d336637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334888, d336637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35016 (p : Pattern) (selected : d334894 p = 0) : d336643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334729 q = 0) : d336558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334729, d336558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34981 q selected
    | true =>
      simp only [d334729, d336558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34982 q selected
  have h2 (q : Pattern) (selected : d334730 q = 0) : d336559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334730, d336559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334730, d336559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334731 q = 0) : d336560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334731, d336560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334731, d336560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334732 q = 0) : d336561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334732, d336561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334732, d336561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334739 q = 0) : d336568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334739, d336568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34983 q selected
    | true =>
      simp only [d334739, d336568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34984 q selected
  have h6 (q : Pattern) (selected : d334740 q = 0) : d336569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334740, d336569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334740, d336569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334741 q = 0) : d336570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334741, d336570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334741, d336570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334758 q = 0) : d336587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334758, d336587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34987 q selected
    | true =>
      simp only [d334758, d336587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34975 q selected
  have h9 (q : Pattern) (selected : d334835 q = 0) : d336535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334835, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34999 q selected
    | true =>
      simp only [d334835, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35000 q selected
  have h10 (q : Pattern) (selected : d334836 q = 0) : d336588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334836, d336588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334836, d336588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334865 q = 0) : d336617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334865, d336617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35006 q selected
    | true =>
      simp only [d334865, d336617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334866 q = 0) : d336618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334866, d336618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334866, d336618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334867 q = 0) : d336619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334867, d336619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334867, d336619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334868 q = 0) : d336620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334868, d336620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334868, d336620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334869 q = 0) : d336621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334869, d336621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334869, d336621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334873 q = 0) : d336625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334873, d336625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35008 q selected
    | true =>
      simp only [d334873, d336625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35009 q selected
  have h17 (q : Pattern) (selected : d334874 q = 0) : d336626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334874, d336626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334874, d336626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334875 q = 0) : d336627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334875, d336627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334875, d336627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d334876 q = 0) : d336628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334876, d336628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334876, d336628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d334879 q = 0) : d336631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334879, d336631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35010 q selected
    | true =>
      simp only [d334879, d336631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35011 q selected
  have h21 (q : Pattern) (selected : d334880 q = 0) : d336632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334880, d336632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334880, d336632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d334881 q = 0) : d336633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334881, d336633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d334881, d336633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d334883 q = 0) : d336635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334883, d336635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35012 q selected
    | true =>
      simp only [d334883, d336635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34978 q selected
  have h24 (q : Pattern) (selected : d334886 q = 0) : d336545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334886, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35013 q selected
    | true =>
      simp only [d334886, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35014 q selected
  have h25 (q : Pattern) (selected : d334887 q = 0) : d336636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334887, d336636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d334887, d336636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d334889 q = 0) : d336638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334889, d336638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35015 q selected
    | true =>
      simp only [d334889, d336638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d334890 q = 0) : d336639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334890, d336639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d334890, d336639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d334891 q = 0) : d336640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334891, d336640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d334891, d336640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d334892 q = 0) : d336641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334892, d336641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d334892, d336641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d334893 q = 0) : d336642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334893, d336642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334893, d336642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d334894 q = 0) : d336643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334894, d336643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334894, d336643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro35017 (p : Pattern) (selected : d334901 p = 0) : d336650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334706 q = 0) : d336535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34975 q selected
    | true =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34976 q selected
  have h2 (q : Pattern) (selected : d334707 q = 0) : d336536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334708 q = 0) : d336537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334709 q = 0) : d336538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334710 q = 0) : d336539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334896 q = 0) : d336645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334896, d336645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34976 q selected
    | true =>
      simp only [d334896, d336645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334897 q = 0) : d336646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334897, d336646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334897, d336646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334898 q = 0) : d336647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334898, d336647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334898, d336647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334899 q = 0) : d336648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334899, d336648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334899, d336648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334900 q = 0) : d336649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334900, d336649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334900, d336649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334901 q = 0) : d336650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334901, d336650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334901, d336650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35018 (p : Pattern) (selected : d334907 p = 0) : d336656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334896 q = 0) : d336645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334896, d336645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34976 q selected
    | true =>
      simp only [d334896, d336645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334897 q = 0) : d336646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334897, d336646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334897, d336646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334898 q = 0) : d336647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334898, d336647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334898, d336647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334899 q = 0) : d336648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334899, d336648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334899, d336648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334900 q = 0) : d336649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334900, d336649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334900, d336649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334902 q = 0) : d336651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334902, d336651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34979 q selected
    | true =>
      simp only [d334902, d336651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334903 q = 0) : d336652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334903, d336652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334903, d336652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334904 q = 0) : d336653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334904, d336653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334904, d336653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334905 q = 0) : d336654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334905, d336654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334905, d336654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334906 q = 0) : d336655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334906, d336655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334906, d336655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334907 q = 0) : d336656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334907, d336656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334907, d336656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35019 (p : Pattern) (selected : d334914 p = 0) : d336663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334883 q = 0) : d336635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334883, d336635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35012 q selected
    | true =>
      simp only [d334883, d336635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34978 q selected
  have h2 (q : Pattern) (selected : d334886 q = 0) : d336545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334886, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35013 q selected
    | true =>
      simp only [d334886, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35014 q selected
  have h3 (q : Pattern) (selected : d334887 q = 0) : d336636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334887, d336636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334887, d336636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334889 q = 0) : d336638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334889, d336638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35015 q selected
    | true =>
      simp only [d334889, d336638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334890 q = 0) : d336639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334890, d336639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334890, d336639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334891 q = 0) : d336640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334891, d336640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334891, d336640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334912 q = 0) : d336661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334912, d336661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334912, d336661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334913 q = 0) : d336662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334913, d336662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334913, d336662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334914 q = 0) : d336663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334914, d336663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334914, d336663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35020 (p : Pattern) (selected : d334916 p = 0) : d336665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334902 q = 0) : d336651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334902, d336651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34979 q selected
    | true =>
      simp only [d334902, d336651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334903 q = 0) : d336652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334903, d336652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334903, d336652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334904 q = 0) : d336653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334904, d336653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334904, d336653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334905 q = 0) : d336654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334905, d336654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334905, d336654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334906 q = 0) : d336655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334906, d336655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334906, d336655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334916 q = 0) : d336665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334916, d336665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334916, d336665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35021 (p : Pattern) (selected : d334936 p = 0) : d336685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334922 q = 0) : d336671 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334922, d336671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334922, d336671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34964 q selected
  have h2 (q : Pattern) (selected : d334634 q = 0) : d336463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334634, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34964 q selected
    | true =>
      simp only [d334634, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334923 q = 0) : d336672 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334923, d336672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334923, d336672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334635 q = 0) : d336464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334635, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334635, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334924 q = 0) : d336673 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334924, d336673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334924, d336673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334925 q = 0) : d336674 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334925, d336674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334925, d336674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334926 q = 0) : d336675 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334926, d336675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334926, d336675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34965 q selected
  have h8 (q : Pattern) (selected : d334641 q = 0) : d336470 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334641, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34965 q selected
    | true =>
      simp only [d334641, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334927 q = 0) : d336676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334927, d336676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334927, d336676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334642 q = 0) : d336471 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334642, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334642, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334928 q = 0) : d336677 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334928, d336677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334928, d336677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334929 q = 0) : d336678 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334929, d336678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334929, d336678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334930 q = 0) : d336679 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334930, d336679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334930, d336679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334931 q = 0) : d336680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
  have h15 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334932 q = 0) : d336681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334933 q = 0) : d336682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334934 q = 0) : d336683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334935 q = 0) : d336684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334935, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334935, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334936 q = 0) : d336685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334936, d336685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334936, d336685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35022 (p : Pattern) (selected : d334941 p = 0) : d336690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334931 q = 0) : d336680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
  have h2 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334932 q = 0) : d336681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334933 q = 0) : d336682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334934 q = 0) : d336683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334935 q = 0) : d336684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334935, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334935, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334940 q = 0) : d336689 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334940, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334940, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334941 q = 0) : d336690 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334941, d336690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334941, d336690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35023 (p : Pattern) (selected : d334955 p = 0) : d336704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334946 q = 0) : d336695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334946, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334946, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
  have h2 (q : Pattern) (selected : d334662 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
    | true =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334947 q = 0) : d336696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334947, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334947, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334663 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334948 q = 0) : d336697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334948, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334948, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334949 q = 0) : d336698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334949, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334949, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334950 q = 0) : d336699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
  have h8 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334951 q = 0) : d336700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334952 q = 0) : d336701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334953 q = 0) : d336702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334954 q = 0) : d336703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334954, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334954, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334931 q = 0) : d336680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334931, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
  have h15 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334932 q = 0) : d336681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334932, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334933 q = 0) : d336682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334933, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334934 q = 0) : d336683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334934, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334940 q = 0) : d336689 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334940, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334940, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334955 q = 0) : d336704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334955, d336704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334955, d336704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35024 (p : Pattern) (selected : d334965 p = 0) : d336714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334950 q = 0) : d336699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
  have h2 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334951 q = 0) : d336700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334952 q = 0) : d336701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334953 q = 0) : d336702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334959 q = 0) : d336708 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334959, d336708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334959, d336708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334960 q = 0) : d336709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334960, d336709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334960, d336709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34971 q selected
  have h9 (q : Pattern) (selected : d334679 q = 0) : d336508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334679, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34971 q selected
    | true =>
      simp only [d334679, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334961 q = 0) : d336710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334961, d336710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334961, d336710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334680 q = 0) : d336509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334680, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334680, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334962 q = 0) : d336711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334962, d336711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334962, d336711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334963 q = 0) : d336712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334963, d336712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334963, d336712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334964 q = 0) : d336713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334964, d336713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334964, d336713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334965 q = 0) : d336714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334965, d336714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334965, d336714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35025 (p : Pattern) (selected : d334971 p = 0) : d336720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334937 q = 0) : d336686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334937, d336686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334937, d336686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35021 q selected
  have h2 (q : Pattern) (selected : d334938 q = 0) : d336687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334938, d336687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334938, d336687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334939 q = 0) : d336688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334939, d336688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334939, d336688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334942 q = 0) : d336691 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334942, d336691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35021 q selected
    | true =>
      simp only [d334942, d336691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35022 q selected
  have h5 (q : Pattern) (selected : d334943 q = 0) : d336692 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334943, d336692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334943, d336692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334944 q = 0) : d336693 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334944, d336693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334944, d336693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334945 q = 0) : d336694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334945, d336694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334945, d336694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334956 q = 0) : d336705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35021 q selected
    | true =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
  have h9 (q : Pattern) (selected : d334957 q = 0) : d336706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334958 q = 0) : d336707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334966 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
    | true =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35024 q selected
  have h12 (q : Pattern) (selected : d334967 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334968 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334969 q = 0) : d336718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334970 q = 0) : d336719 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334970, d336719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334970, d336719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334971 q = 0) : d336720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334971, d336720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334971, d336720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro35026 (p : Pattern) (selected : d334976 p = 0) : d336725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334956 q = 0) : d336705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35021 q selected
    | true =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
  have h2 (q : Pattern) (selected : d334957 q = 0) : d336706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334958 q = 0) : d336707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334966 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
    | true =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35024 q selected
  have h5 (q : Pattern) (selected : d334967 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334968 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334969 q = 0) : d336718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334974 q = 0) : d336723 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334974, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334974, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334975 q = 0) : d336724 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334975, d336724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334975, d336724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334976 q = 0) : d336725 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334976, d336725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334976, d336725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35027 (p : Pattern) (selected : d334982 p = 0) : d336731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334972 q = 0) : d336721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334972, d336721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35025 q selected
    | true =>
      simp only [d334972, d336721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334973 q = 0) : d336722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334973, d336722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334973, d336722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334977 q = 0) : d336726 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334977, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35026 q selected
    | true =>
      simp only [d334977, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334978 q = 0) : d336727 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334978, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334978, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334979 q = 0) : d336728 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334979, d336728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334979, d336728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334980 q = 0) : d336729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334980, d336729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334980, d336729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334981 q = 0) : d336730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334981, d336730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334981, d336730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334982 q = 0) : d336731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334982, d336731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334982, d336731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35028 (p : Pattern) (selected : d334984 p = 0) : d336733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334966 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
    | true =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35024 q selected
  have h2 (q : Pattern) (selected : d334967 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334968 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334974 q = 0) : d336723 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334974, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334974, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334983 q = 0) : d336732 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334983, d336732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334983, d336732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334984 q = 0) : d336733 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334984, d336733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334984, d336733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35029 (p : Pattern) (selected : d334990 p = 0) : d336739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334977 q = 0) : d336726 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334977, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35026 q selected
    | true =>
      simp only [d334977, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334978 q = 0) : d336727 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334978, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334978, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334985 q = 0) : d336734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334985, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35028 q selected
    | true =>
      simp only [d334985, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334986 q = 0) : d336735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334986, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334986, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334987 q = 0) : d336736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334987, d336736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334987, d336736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334988 q = 0) : d336737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334988, d336737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334988, d336737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334989 q = 0) : d336738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334989, d336738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334989, d336738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334990 q = 0) : d336739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334990, d336739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334990, d336739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35030 (p : Pattern) (selected : d335006 p = 0) : d336685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334992 q = 0) : d336671 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334992, d336671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334992, d336671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34988 q selected
  have h2 (q : Pattern) (selected : d334763 q = 0) : d336463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334763, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34988 q selected
    | true =>
      simp only [d334763, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334993 q = 0) : d336672 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334993, d336672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334993, d336672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334764 q = 0) : d336464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334764, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334764, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334994 q = 0) : d336673 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334994, d336673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334994, d336673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334995 q = 0) : d336674 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334995, d336674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334995, d336674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334996 q = 0) : d336675 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334996, d336675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334996, d336675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34989 q selected
  have h8 (q : Pattern) (selected : d334770 q = 0) : d336470 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334770, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34989 q selected
    | true =>
      simp only [d334770, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334997 q = 0) : d336676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334997, d336676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334997, d336676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334771 q = 0) : d336471 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334771, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334771, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334998 q = 0) : d336677 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334998, d336677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334998, d336677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334999 q = 0) : d336678 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334999, d336678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334999, d336678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335000 q = 0) : d336679 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335000, d336679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335000, d336679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335001 q = 0) : d336680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335001, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335001, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
  have h15 (q : Pattern) (selected : d334781 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
    | true =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335002 q = 0) : d336681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335002, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335002, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334782 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335003 q = 0) : d336682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335003, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335003, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335004 q = 0) : d336683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335004, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335004, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335005 q = 0) : d336684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335005, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335005, d336684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d335006 q = 0) : d336685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335006, d336685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335006, d336685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35031 (p : Pattern) (selected : d335017 p = 0) : d336704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335007 q = 0) : d336695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335007, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335007, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34992 q selected
  have h2 (q : Pattern) (selected : d334791 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334791, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34992 q selected
    | true =>
      simp only [d334791, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335008 q = 0) : d336696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335008, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335008, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334792 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334792, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334792, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335009 q = 0) : d336697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335009, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335009, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335010 q = 0) : d336698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335010, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335010, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335011 q = 0) : d336699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335011, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335011, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
  have h8 (q : Pattern) (selected : d334796 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
    | true =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335012 q = 0) : d336700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335012, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335012, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334797 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335013 q = 0) : d336701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335013, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335013, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d335014 q = 0) : d336702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335014, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335014, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335015 q = 0) : d336703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335015, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335015, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335001 q = 0) : d336680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335001, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335001, d336680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
  have h15 (q : Pattern) (selected : d334781 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
    | true =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335002 q = 0) : d336681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335002, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335002, d336681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334782 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335003 q = 0) : d336682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335003, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335003, d336682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335004 q = 0) : d336683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335004, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335004, d336683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335016 q = 0) : d336689 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335016, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335016, d336689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335017 q = 0) : d336704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335017, d336704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335017, d336704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35032 (p : Pattern) (selected : d335027 p = 0) : d336714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335011 q = 0) : d336699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335011, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335011, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
  have h2 (q : Pattern) (selected : d334796 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
    | true =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335012 q = 0) : d336700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335012, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335012, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334797 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335013 q = 0) : d336701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335013, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335013, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335014 q = 0) : d336702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335014, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335014, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335021 q = 0) : d336708 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335021, d336708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335021, d336708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335022 q = 0) : d336709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335022, d336709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335022, d336709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34995 q selected
  have h9 (q : Pattern) (selected : d334808 q = 0) : d336508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334808, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34995 q selected
    | true =>
      simp only [d334808, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335023 q = 0) : d336710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335023, d336710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335023, d336710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334809 q = 0) : d336509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334809, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334809, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335024 q = 0) : d336711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335024, d336711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335024, d336711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335025 q = 0) : d336712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335025, d336712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335025, d336712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335026 q = 0) : d336713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335026, d336713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335026, d336713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335027 q = 0) : d336714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335027, d336714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335027, d336714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35033 (p : Pattern) (selected : d335034 p = 0) : d336725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335018 q = 0) : d336705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335018, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35030 q selected
    | true =>
      simp only [d335018, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35031 q selected
  have h2 (q : Pattern) (selected : d335019 q = 0) : d336706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335019, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335019, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335020 q = 0) : d336707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335020, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335020, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335028 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335028, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35031 q selected
    | true =>
      simp only [d335028, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35032 q selected
  have h5 (q : Pattern) (selected : d335029 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335029, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335029, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335030 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335030, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335030, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335031 q = 0) : d336718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335031, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335031, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335032 q = 0) : d336723 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335032, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335032, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335033 q = 0) : d336724 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335033, d336724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335033, d336724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335034 q = 0) : d336725 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335034, d336725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335034, d336725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35034 (p : Pattern) (selected : d335038 p = 0) : d336733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335028 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335028, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35031 q selected
    | true =>
      simp only [d335028, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35032 q selected
  have h2 (q : Pattern) (selected : d335029 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335029, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335029, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335030 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335030, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335030, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335032 q = 0) : d336723 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335032, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335032, d336723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335037 q = 0) : d336732 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335037, d336732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335037, d336732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335038 q = 0) : d336733 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335038, d336733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335038, d336733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35035 (p : Pattern) (selected : d335044 p = 0) : d336739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335035 q = 0) : d336726 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335035, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35033 q selected
    | true =>
      simp only [d335035, d336726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335036 q = 0) : d336727 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335036, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335036, d336727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335039 q = 0) : d336734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335039, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35034 q selected
    | true =>
      simp only [d335039, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335040 q = 0) : d336735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335040, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335040, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335041 q = 0) : d336736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335041, d336736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335041, d336736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335042 q = 0) : d336737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335042, d336737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335042, d336737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335043 q = 0) : d336738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335043, d336738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335043, d336738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335044 q = 0) : d336739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335044, d336739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335044, d336739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35036 (p : Pattern) (selected : d335048 p = 0) : d336744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335039 q = 0) : d336734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335039, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35034 q selected
    | true =>
      simp only [d335039, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335040 q = 0) : d336735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335040, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335040, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335045 q = 0) : d336741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335045, d336741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335045, d336741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335046 q = 0) : d336742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335046, d336742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335046, d336742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335047 q = 0) : d336743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335047, d336743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335047, d336743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335048 q = 0) : d336744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335048, d336744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335048, d336744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35037 (p : Pattern) (selected : d335056 p = 0) : d336752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334946 q = 0) : d336695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334946, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334946, d336695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
  have h2 (q : Pattern) (selected : d334662 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
    | true =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334947 q = 0) : d336696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334947, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334947, d336696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334663 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334948 q = 0) : d336697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334948, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334948, d336697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334949 q = 0) : d336698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334949, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334949, d336698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334950 q = 0) : d336699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334950, d336699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
  have h8 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334951 q = 0) : d336700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334951, d336700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334952 q = 0) : d336701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334952, d336701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334953 q = 0) : d336702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334953, d336702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334954 q = 0) : d336703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334954, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334954, d336703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335051 q = 0) : d336747 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335051, d336747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335051, d336747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35001 q selected
  have h15 (q : Pattern) (selected : d334840 q = 0) : d336592 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334840, d336592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35001 q selected
    | true =>
      simp only [d334840, d336592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335052 q = 0) : d336748 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335052, d336748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335052, d336748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334841 q = 0) : d336593 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334841, d336593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334841, d336593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335053 q = 0) : d336749 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335053, d336749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335053, d336749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335054 q = 0) : d336750 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335054, d336750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335054, d336750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335055 q = 0) : d336751 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335055, d336751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335055, d336751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335056 q = 0) : d336752 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335056, d336752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335056, d336752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35038 (p : Pattern) (selected : d335062 p = 0) : d336758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335057 q = 0) : d336753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335057, d336753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335057, d336753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35003 q selected
  have h2 (q : Pattern) (selected : d334847 q = 0) : d336599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334847, d336599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35003 q selected
    | true =>
      simp only [d334847, d336599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335058 q = 0) : d336754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335058, d336754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335058, d336754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334848 q = 0) : d336600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334848, d336600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334848, d336600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335059 q = 0) : d336755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335059, d336755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335059, d336755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335060 q = 0) : d336756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335060, d336756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335060, d336756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335061 q = 0) : d336757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335061, d336757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335061, d336757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335062 q = 0) : d336758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335062, d336758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335062, d336758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35039 (p : Pattern) (selected : d335068 p = 0) : d336764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334956 q = 0) : d336705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35021 q selected
    | true =>
      simp only [d334956, d336705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
  have h2 (q : Pattern) (selected : d334957 q = 0) : d336706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334957, d336706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334958 q = 0) : d336707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334958, d336707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334966 q = 0) : d336715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35023 q selected
    | true =>
      simp only [d334966, d336715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35024 q selected
  have h5 (q : Pattern) (selected : d334967 q = 0) : d336716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334967, d336716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334968 q = 0) : d336717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334968, d336717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334969 q = 0) : d336718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334969, d336718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335063 q = 0) : d336759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335063, d336759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35037 q selected
    | true =>
      simp only [d335063, d336759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35038 q selected
  have h9 (q : Pattern) (selected : d335064 q = 0) : d336760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335064, d336760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335064, d336760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335065 q = 0) : d336761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335065, d336761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335065, d336761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335066 q = 0) : d336762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335066, d336762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335066, d336762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335067 q = 0) : d336763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335067, d336763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335067, d336763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335068 q = 0) : d336764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335068, d336764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335068, d336764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro35040 (p : Pattern) (selected : d335074 p = 0) : d336770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335069 q = 0) : d336765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335069, d336765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35039 q selected
    | true =>
      simp only [d335069, d336765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335070 q = 0) : d336766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335070, d336766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335070, d336766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335071 q = 0) : d336767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335071, d336767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335071, d336767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335072 q = 0) : d336768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335072, d336768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335072, d336768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335073 q = 0) : d336769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335073, d336769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335073, d336769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335074 q = 0) : d336770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335074, d336770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335074, d336770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35041 (p : Pattern) (selected : d335080 p = 0) : d336776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334991 q = 0) : d336740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334991, d336740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35027 q selected
    | true =>
      simp only [d334991, d336740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35029 q selected
  have h2 (q : Pattern) (selected : d335049 q = 0) : d336745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335049, d336745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35035 q selected
    | true =>
      simp only [d335049, d336745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35036 q selected
  have h3 (q : Pattern) (selected : d335050 q = 0) : d336746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335050, d336746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335050, d336746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335075 q = 0) : d336771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335075, d336771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35040 q selected
    | true =>
      simp only [d335075, d336771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335076 q = 0) : d336772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335076, d336772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335076, d336772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335077 q = 0) : d336773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335077, d336773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335077, d336773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335078 q = 0) : d336774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335078, d336774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335078, d336774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335079 q = 0) : d336775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335079, d336775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335079, d336775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335080 q = 0) : d336776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335080, d336776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335080, d336776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35042 (p : Pattern) (selected : d335085 p = 0) : d336744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334985 q = 0) : d336734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334985, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35028 q selected
    | true =>
      simp only [d334985, d336734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334986 q = 0) : d336735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334986, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334986, d336735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335082 q = 0) : d336741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335082, d336741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335082, d336741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335083 q = 0) : d336742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335083, d336742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335083, d336742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335084 q = 0) : d336743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335084, d336743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335084, d336743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335085 q = 0) : d336744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335085, d336744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335085, d336744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35043 (p : Pattern) (selected : d335091 p = 0) : d336783 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335086 q = 0) : d336778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335086, d336778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35042 q selected
    | true =>
      simp only [d335086, d336778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335087 q = 0) : d336779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335087, d336779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335087, d336779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335088 q = 0) : d336780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335088, d336780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335088, d336780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335089 q = 0) : d336781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335089, d336781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335089, d336781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335090 q = 0) : d336782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335090, d336782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335090, d336782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335091 q = 0) : d336783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335091, d336783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335091, d336783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35044 (p : Pattern) (selected : d335097 p = 0) : d336789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334712 q = 0) : d336541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334712, d336541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334712, d336541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34977 q selected
  have h2 (q : Pattern) (selected : d334713 q = 0) : d336542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334713, d336542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334713, d336542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334722 q = 0) : d336551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334722, d336551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34977 q selected
    | true =>
      simp only [d334722, d336551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34980 q selected
  have h4 (q : Pattern) (selected : d334723 q = 0) : d336552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334723, d336552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334723, d336552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334724 q = 0) : d336553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334724, d336553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334724, d336553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334895 q = 0) : d336644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334895, d336644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35007 q selected
    | true =>
      simp only [d334895, d336644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35016 q selected
  have h7 (q : Pattern) (selected : d334908 q = 0) : d336657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334908, d336657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35017 q selected
    | true =>
      simp only [d334908, d336657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35018 q selected
  have h8 (q : Pattern) (selected : d334909 q = 0) : d336658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334909, d336658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334909, d336658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334910 q = 0) : d336659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334910, d336659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334910, d336659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334911 q = 0) : d336660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334911, d336660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334911, d336660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334915 q = 0) : d336664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334915, d336664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334915, d336664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35019 q selected
  have h12 (q : Pattern) (selected : d334917 q = 0) : d336666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334917, d336666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334917, d336666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35020 q selected
  have h13 (q : Pattern) (selected : d334918 q = 0) : d336667 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334918, d336667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334918, d336667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334919 q = 0) : d336668 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334919, d336668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334919, d336668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334920 q = 0) : d336669 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334920, d336669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334920, d336669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334921 q = 0) : d336670 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334921, d336670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334921, d336670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335081 q = 0) : d336777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335081, d336777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335081, d336777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35041 q selected
  have h18 (q : Pattern) (selected : d335092 q = 0) : d336784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335092, d336784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335092, d336784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35043 q selected
  have h19 (q : Pattern) (selected : d335093 q = 0) : d336785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335093, d336785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d335093, d336785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d335094 q = 0) : d336786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335094, d336786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335094, d336786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335095 q = 0) : d336787 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d335095, d336787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d335095, d336787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d335096 q = 0) : d336788 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d335096, d336788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d335096, d336788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d335097 q = 0) : d336789 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d335097, d336789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335097, d336789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro35045 (p : Pattern) (selected : d335103 p = 0) : d336795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335098 q = 0) : d336790 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d335098, d336790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335098, d336790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35044 q selected
  have h2 (q : Pattern) (selected : d335099 q = 0) : d336791 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d335099, d336791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335099, d336791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335100 q = 0) : d336792 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d335100, d336792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335100, d336792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335101 q = 0) : d336793 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d335101, d336793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335101, d336793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335102 q = 0) : d336794 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d335102, d336794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335102, d336794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335103 q = 0) : d336795 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d335103, d336795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335103, d336795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35046 (p : Pattern) (selected : d335111 p = 0) : d336803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335108 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
    | true =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h2 (q : Pattern) (selected : d335109 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335110 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335111 q = 0) : d336803 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335111, d336803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335111, d336803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35047 (p : Pattern) (selected : d335117 p = 0) : d336809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335114 q = 0) : d336806 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335115 q = 0) : d336807 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335116 q = 0) : d336808 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335116, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335116, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335117 q = 0) : d336809 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335117, d336809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335117, d336809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35048 (p : Pattern) (selected : d335121 p = 0) : d336813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335118 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335119 q = 0) : d336811 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335120 q = 0) : d336812 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335121 q = 0) : d336813 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335121, d336813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335121, d336813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35049 (p : Pattern) (selected : d335126 p = 0) : d336818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335118 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335119 q = 0) : d336811 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335120 q = 0) : d336812 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335108 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
    | true =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h5 (q : Pattern) (selected : d335109 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335110 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335126 q = 0) : d336818 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335126, d336818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335126, d336818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35050 (p : Pattern) (selected : d335133 p = 0) : d336825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335122 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
    | true =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335123 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335124 q = 0) : d336816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335124, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335124, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335125 q = 0) : d336817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335125, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335125, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335129 q = 0) : d336821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335130 q = 0) : d336822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335131 q = 0) : d336823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335131, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335131, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335114 q = 0) : d336806 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335115 q = 0) : d336807 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335132 q = 0) : d336824 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335132, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335132, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335133 q = 0) : d336825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335133, d336825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335133, d336825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35051 (p : Pattern) (selected : d335138 p = 0) : d336830 p = 1 := by
  have h0 (q : Pattern) (selected : d335108 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
    | true =>
      simp only [d335108, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d335109 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335109, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335110 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335110, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d335138 q = 0) : d336830 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335138, d336830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335138, d336830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro35052 (p : Pattern) (selected : d335144 p = 0) : d336836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335129 q = 0) : d336821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335130 q = 0) : d336822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335137 q = 0) : d336829 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335137, d336829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335137, d336829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335139 q = 0) : d336831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335139, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35051 q selected
    | true =>
      simp only [d335139, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335140 q = 0) : d336832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335140, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335140, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335141 q = 0) : d336833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335141, d336833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335141, d336833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335142 q = 0) : d336834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335142, d336834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335142, d336834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335143 q = 0) : d336835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335143, d336835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335143, d336835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335144 q = 0) : d336836 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335144, d336836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335144, d336836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35053 (p : Pattern) (selected : d335151 p = 0) : d336843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335134 q = 0) : d336826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35047 q selected
    | true =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
  have h2 (q : Pattern) (selected : d335135 q = 0) : d336827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335136 q = 0) : d336828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335145 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
    | true =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35052 q selected
  have h5 (q : Pattern) (selected : d335146 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335147 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335148 q = 0) : d336840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335149 q = 0) : d336841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335149, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335149, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335150 q = 0) : d336842 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335150, d336842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335150, d336842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335151 q = 0) : d336843 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335151, d336843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335151, d336843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35054 (p : Pattern) (selected : d335155 p = 0) : d336847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335145 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
    | true =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35052 q selected
  have h2 (q : Pattern) (selected : d335146 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335147 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335149 q = 0) : d336841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335149, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335149, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335154 q = 0) : d336846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335154, d336846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335154, d336846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335155 q = 0) : d336847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335155, d336847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335155, d336847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35055 (p : Pattern) (selected : d335161 p = 0) : d336853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335159 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335160 q = 0) : d336852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335160, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335160, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335161 q = 0) : d336853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335161, d336853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335161, d336853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35056 (p : Pattern) (selected : d335165 p = 0) : d336857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335163 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335164 q = 0) : d336856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335164, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335164, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335165 q = 0) : d336857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335165, d336857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335165, d336857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35057 (p : Pattern) (selected : d335171 p = 0) : d336863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335166 q = 0) : d336858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35055 q selected
    | true =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35056 q selected
  have h2 (q : Pattern) (selected : d335167 q = 0) : d336859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335168 q = 0) : d336860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335169 q = 0) : d336861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335170 q = 0) : d336862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335171 q = 0) : d336863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335171, d336863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335171, d336863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35058 (p : Pattern) (selected : d335174 p = 0) : d336866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335159 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335160 q = 0) : d336852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335160, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335160, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335174 q = 0) : d336866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335174, d336866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335174, d336866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35059 (p : Pattern) (selected : d335175 p = 0) : d336867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335163 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335164 q = 0) : d336856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335164, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335164, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335175 q = 0) : d336867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335175, d336867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335175, d336867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35060 (p : Pattern) (selected : d335181 p = 0) : d336873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335166 q = 0) : d336858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35055 q selected
    | true =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35056 q selected
  have h2 (q : Pattern) (selected : d335167 q = 0) : d336859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335168 q = 0) : d336860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335169 q = 0) : d336861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335170 q = 0) : d336862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335176 q = 0) : d336868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335176, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35058 q selected
    | true =>
      simp only [d335176, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35059 q selected
  have h7 (q : Pattern) (selected : d335177 q = 0) : d336869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335177, d336869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335177, d336869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335178 q = 0) : d336870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335178, d336870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335178, d336870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335179 q = 0) : d336871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335179, d336871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335179, d336871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335180 q = 0) : d336872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335180, d336872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335180, d336872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335181 q = 0) : d336873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335181, d336873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335181, d336873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35061 (p : Pattern) (selected : d335186 p = 0) : d336878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335159 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335185 q = 0) : d336877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335185, d336877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335185, d336877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335186 q = 0) : d336878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335186, d336878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335186, d336878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35062 (p : Pattern) (selected : d335188 p = 0) : d336880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335163 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335187 q = 0) : d336879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335187, d336879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335187, d336879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335188 q = 0) : d336880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335188, d336880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335188, d336880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35063 (p : Pattern) (selected : d335195 p = 0) : d336887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335193 q = 0) : d336885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335193, d336885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335193, d336885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335194 q = 0) : d336886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335194, d336886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335194, d336886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335195 q = 0) : d336887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335195, d336887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335195, d336887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35064 (p : Pattern) (selected : d335198 p = 0) : d336890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335196 q = 0) : d336888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335196, d336888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335196, d336888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335197 q = 0) : d336889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335197, d336889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335197, d336889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335198 q = 0) : d336890 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335198, d336890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335198, d336890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35065 (p : Pattern) (selected : d335205 p = 0) : d336897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335114 q = 0) : d336806 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335114, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335115 q = 0) : d336807 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335115, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335116 q = 0) : d336808 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335116, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335116, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335132 q = 0) : d336824 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335132, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335132, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335205 q = 0) : d336897 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335205, d336897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335205, d336897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35066 (p : Pattern) (selected : d335211 p = 0) : d336903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335202 q = 0) : d336894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335202, d336894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335202, d336894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35047 q selected
  have h2 (q : Pattern) (selected : d335203 q = 0) : d336895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335203, d336895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335203, d336895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335204 q = 0) : d336896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335204, d336896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335204, d336896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335206 q = 0) : d336898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335206, d336898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35047 q selected
    | true =>
      simp only [d335206, d336898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35065 q selected
  have h5 (q : Pattern) (selected : d335207 q = 0) : d336899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335207, d336899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335207, d336899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335208 q = 0) : d336900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335208, d336900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335208, d336900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335209 q = 0) : d336901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335209, d336901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335209, d336901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335134 q = 0) : d336826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35047 q selected
    | true =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
  have h9 (q : Pattern) (selected : d335135 q = 0) : d336827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335136 q = 0) : d336828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335145 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
    | true =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35052 q selected
  have h12 (q : Pattern) (selected : d335146 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335147 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335148 q = 0) : d336840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d335210 q = 0) : d336902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335210, d336902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335210, d336902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335211 q = 0) : d336903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335211, d336903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335211, d336903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro35067 (p : Pattern) (selected : d335217 p = 0) : d336909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335212 q = 0) : d336904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335212, d336904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35066 q selected
    | true =>
      simp only [d335212, d336904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335213 q = 0) : d336905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335213, d336905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335213, d336905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335214 q = 0) : d336906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335214, d336906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335214, d336906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335215 q = 0) : d336907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335215, d336907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335215, d336907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335216 q = 0) : d336908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335216, d336908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335216, d336908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335217 q = 0) : d336909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335217, d336909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335217, d336909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35068 (p : Pattern) (selected : d335222 p = 0) : d336803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335219 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
    | true =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h2 (q : Pattern) (selected : d335220 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335221 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335222 q = 0) : d336803 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335222, d336803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335222, d336803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35069 (p : Pattern) (selected : d335228 p = 0) : d336809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335223 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
    | true =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335224 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335225 q = 0) : d336806 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335225, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335225, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335226 q = 0) : d336807 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335226, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335226, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335227 q = 0) : d336808 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335227, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335227, d336808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335228 q = 0) : d336809 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335228, d336809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335228, d336809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35070 (p : Pattern) (selected : d335232 p = 0) : d336813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335229 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335229, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d335229, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335230 q = 0) : d336811 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335230, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335230, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335231 q = 0) : d336812 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335231, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335231, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335232 q = 0) : d336813 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335232, d336813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335232, d336813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35071 (p : Pattern) (selected : d335237 p = 0) : d336818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335229 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335229, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d335229, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335230 q = 0) : d336811 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335230, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335230, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335231 q = 0) : d336812 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335231, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335231, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335219 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
    | true =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h5 (q : Pattern) (selected : d335220 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335221 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335237 q = 0) : d336818 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335237, d336818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335237, d336818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35072 (p : Pattern) (selected : d335244 p = 0) : d336825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335233 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335233, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35070 q selected
    | true =>
      simp only [d335233, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335234 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335234, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335234, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335235 q = 0) : d336816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335235, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335235, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335236 q = 0) : d336817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335236, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335236, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335238 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
    | true =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335239 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335240 q = 0) : d336821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335240, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335240, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335241 q = 0) : d336822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335241, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335241, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335242 q = 0) : d336823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335242, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335242, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335223 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
    | true =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335224 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335225 q = 0) : d336806 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335225, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335225, d336806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335226 q = 0) : d336807 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335226, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335226, d336807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335243 q = 0) : d336824 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335243, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335243, d336824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335244 q = 0) : d336825 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335244, d336825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335244, d336825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35073 (p : Pattern) (selected : d335249 p = 0) : d336830 p = 1 := by
  have h0 (q : Pattern) (selected : d335219 q = 0) : d336800 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
    | true =>
      simp only [d335219, d336800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d335220 q = 0) : d336801 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335220, d336801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335221 q = 0) : d336802 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335221, d336802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d335249 q = 0) : d336830 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335249, d336830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335249, d336830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro35074 (p : Pattern) (selected : d335255 p = 0) : d336836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335238 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
    | true =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335239 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335240 q = 0) : d336821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335240, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335240, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335241 q = 0) : d336822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335241, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335241, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335248 q = 0) : d336829 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335248, d336829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335248, d336829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335250 q = 0) : d336831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335250, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35073 q selected
    | true =>
      simp only [d335250, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335251 q = 0) : d336832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335251, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335251, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335252 q = 0) : d336833 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335252, d336833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335252, d336833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335253 q = 0) : d336834 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335253, d336834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335253, d336834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335254 q = 0) : d336835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335254, d336835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335254, d336835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335255 q = 0) : d336836 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335255, d336836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335255, d336836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35075 (p : Pattern) (selected : d335262 p = 0) : d336843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335245 q = 0) : d336826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335245, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35069 q selected
    | true =>
      simp only [d335245, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35072 q selected
  have h2 (q : Pattern) (selected : d335246 q = 0) : d336827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335246, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335246, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335247 q = 0) : d336828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335247, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335247, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335256 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335256, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35072 q selected
    | true =>
      simp only [d335256, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35074 q selected
  have h5 (q : Pattern) (selected : d335257 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335257, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335257, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335258 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335258, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335258, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335259 q = 0) : d336840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335259, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335259, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335260 q = 0) : d336841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335260, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335260, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335261 q = 0) : d336842 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335261, d336842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335261, d336842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335262 q = 0) : d336843 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335262, d336843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335262, d336843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35076 (p : Pattern) (selected : d335266 p = 0) : d336847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335256 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335256, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35072 q selected
    | true =>
      simp only [d335256, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35074 q selected
  have h2 (q : Pattern) (selected : d335257 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335257, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335257, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335258 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335258, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335258, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335260 q = 0) : d336841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335260, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335260, d336841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335265 q = 0) : d336846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335265, d336846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335265, d336846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335266 q = 0) : d336847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335266, d336847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335266, d336847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35077 (p : Pattern) (selected : d335272 p = 0) : d336853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335263 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335263, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35075 q selected
    | true =>
      simp only [d335263, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335264 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335264, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335264, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335267 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35076 q selected
    | true =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335268 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335269 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335269, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335269, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335270 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335270, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335270, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335271 q = 0) : d336852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335271, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335271, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335272 q = 0) : d336853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335272, d336853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335272, d336853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35078 (p : Pattern) (selected : d335276 p = 0) : d336857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335267 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35076 q selected
    | true =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335268 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335273 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335273, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335273, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335274 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335274, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335274, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335275 q = 0) : d336856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335275, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335275, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335276 q = 0) : d336857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335276, d336857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335276, d336857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35079 (p : Pattern) (selected : d335281 p = 0) : d336914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335118 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335279 q = 0) : d336912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335279, d336912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335279, d336912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335280 q = 0) : d336913 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335280, d336913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335280, d336913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335281 q = 0) : d336914 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335281, d336914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335281, d336914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35080 (p : Pattern) (selected : d335287 p = 0) : d336920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335122 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
    | true =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335123 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335124 q = 0) : d336816 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335124, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335124, d336816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335125 q = 0) : d336817 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335125, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335125, d336817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335129 q = 0) : d336821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335129, d336821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335130 q = 0) : d336822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335130, d336822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335131 q = 0) : d336823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335131, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335131, d336823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335282 q = 0) : d336915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335282, d336915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35079 q selected
    | true =>
      simp only [d335282, d336915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335283 q = 0) : d336916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335283, d336916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335283, d336916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335284 q = 0) : d336917 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335284, d336917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335284, d336917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335285 q = 0) : d336918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335285, d336918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335285, d336918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335286 q = 0) : d336919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335286, d336919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335286, d336919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335287 q = 0) : d336920 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335287, d336920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335287, d336920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35081 (p : Pattern) (selected : d335288 p = 0) : d336921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335118 q = 0) : d336810 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d335118, d336810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335119 q = 0) : d336811 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335119, d336811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335120 q = 0) : d336812 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335120, d336812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335279 q = 0) : d336912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335279, d336912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335279, d336912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335280 q = 0) : d336913 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335280, d336913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335280, d336913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335288 q = 0) : d336921 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335288, d336921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335288, d336921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35082 (p : Pattern) (selected : d335294 p = 0) : d336927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335289 q = 0) : d336922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335289, d336922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35081 q selected
    | true =>
      simp only [d335289, d336922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335290 q = 0) : d336923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335290, d336923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335290, d336923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335291 q = 0) : d336924 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335291, d336924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335291, d336924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335292 q = 0) : d336925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335292, d336925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335292, d336925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335293 q = 0) : d336926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335293, d336926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335293, d336926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335294 q = 0) : d336927 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335294, d336927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335294, d336927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35083 (p : Pattern) (selected : d335300 p = 0) : d336933 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335134 q = 0) : d336826 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35047 q selected
    | true =>
      simp only [d335134, d336826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
  have h2 (q : Pattern) (selected : d335135 q = 0) : d336827 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335135, d336827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335136 q = 0) : d336828 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335136, d336828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335145 q = 0) : d336837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35050 q selected
    | true =>
      simp only [d335145, d336837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35052 q selected
  have h5 (q : Pattern) (selected : d335146 q = 0) : d336838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335146, d336838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335147 q = 0) : d336839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335147, d336839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335148 q = 0) : d336840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335148, d336840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335295 q = 0) : d336928 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335295, d336928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35080 q selected
    | true =>
      simp only [d335295, d336928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35082 q selected
  have h9 (q : Pattern) (selected : d335296 q = 0) : d336929 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335296, d336929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335296, d336929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335297 q = 0) : d336930 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335297, d336930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335297, d336930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335298 q = 0) : d336931 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335298, d336931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335298, d336931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335299 q = 0) : d336932 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335299, d336932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335299, d336932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335300 q = 0) : d336933 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335300, d336933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335300, d336933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro35084 (p : Pattern) (selected : d335306 p = 0) : d336939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335301 q = 0) : d336934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335301, d336934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35083 q selected
    | true =>
      simp only [d335301, d336934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335302 q = 0) : d336935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335302, d336935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335302, d336935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335303 q = 0) : d336936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335303, d336936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335303, d336936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335304 q = 0) : d336937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335304, d336937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335304, d336937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335305 q = 0) : d336938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335305, d336938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335305, d336938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335306 q = 0) : d336939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335306, d336939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335306, d336939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35085 (p : Pattern) (selected : d335312 p = 0) : d336945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335189 q = 0) : d336881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335189, d336881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35061 q selected
    | true =>
      simp only [d335189, d336881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35062 q selected
  have h2 (q : Pattern) (selected : d335190 q = 0) : d336882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335190, d336882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335190, d336882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335191 q = 0) : d336883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335191, d336883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335191, d336883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335192 q = 0) : d336884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335192, d336884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335192, d336884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335199 q = 0) : d336891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335199, d336891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35063 q selected
    | true =>
      simp only [d335199, d336891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35064 q selected
  have h6 (q : Pattern) (selected : d335200 q = 0) : d336892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335200, d336892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335200, d336892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335201 q = 0) : d336893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335201, d336893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335201, d336893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335218 q = 0) : d336910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335218, d336910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35067 q selected
    | true =>
      simp only [d335218, d336910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35055 q selected
  have h9 (q : Pattern) (selected : d335277 q = 0) : d336858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335277, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35077 q selected
    | true =>
      simp only [d335277, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35078 q selected
  have h10 (q : Pattern) (selected : d335278 q = 0) : d336911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335278, d336911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335278, d336911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335307 q = 0) : d336940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335307, d336940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35084 q selected
    | true =>
      simp only [d335307, d336940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335308 q = 0) : d336941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335308, d336941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335308, d336941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335309 q = 0) : d336942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335309, d336942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335309, d336942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335310 q = 0) : d336943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335310, d336943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335310, d336943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d335311 q = 0) : d336944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335311, d336944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335311, d336944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335312 q = 0) : d336945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335312, d336945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335312, d336945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro35086 (p : Pattern) (selected : d335313 p = 0) : d336946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335159 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335159, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335185 q = 0) : d336877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335185, d336877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335185, d336877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335313 q = 0) : d336946 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335313, d336946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335313, d336946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35087 (p : Pattern) (selected : d335314 p = 0) : d336947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335163 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335163, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335187 q = 0) : d336879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335187, d336879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335187, d336879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335314 q = 0) : d336947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335314, d336947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335314, d336947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35088 (p : Pattern) (selected : d335319 p = 0) : d336952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335158 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335158, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335193 q = 0) : d336885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335193, d336885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335193, d336885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335194 q = 0) : d336886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335194, d336886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335194, d336886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335319 q = 0) : d336952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335319, d336952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335319, d336952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35089 (p : Pattern) (selected : d335320 p = 0) : d336953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335156 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35054 q selected
    | true =>
      simp only [d335156, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335157 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335157, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335162 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335162, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335196 q = 0) : d336888 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335196, d336888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335196, d336888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335197 q = 0) : d336889 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335197, d336889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335197, d336889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335320 q = 0) : d336953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335320, d336953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335320, d336953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35090 (p : Pattern) (selected : d335324 p = 0) : d336957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335212 q = 0) : d336904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335212, d336904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35066 q selected
    | true =>
      simp only [d335212, d336904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335213 q = 0) : d336905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335213, d336905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335213, d336905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335152 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35053 q selected
    | true =>
      simp only [d335152, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335153 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335153, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335214 q = 0) : d336906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335214, d336906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335214, d336906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335215 q = 0) : d336907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335215, d336907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335215, d336907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335216 q = 0) : d336908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335216, d336908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335216, d336908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335324 q = 0) : d336957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335324, d336957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335324, d336957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35091 (p : Pattern) (selected : d335326 p = 0) : d336866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335263 q = 0) : d336844 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335263, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35075 q selected
    | true =>
      simp only [d335263, d336844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335264 q = 0) : d336845 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335264, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335264, d336845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335267 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35076 q selected
    | true =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335268 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335269 q = 0) : d336850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335269, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335269, d336850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335270 q = 0) : d336851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335270, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335270, d336851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335271 q = 0) : d336852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335271, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335271, d336852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335326 q = 0) : d336866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335326, d336866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335326, d336866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35092 (p : Pattern) (selected : d335327 p = 0) : d336867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335267 q = 0) : d336848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35076 q selected
    | true =>
      simp only [d335267, d336848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335268 q = 0) : d336849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, d336849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335273 q = 0) : d336854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335273, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335273, d336854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335274 q = 0) : d336855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335274, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335274, d336855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335275 q = 0) : d336856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335275, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335275, d336856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335327 q = 0) : d336867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335327, d336867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335327, d336867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35093 (p : Pattern) (selected : d335330 p = 0) : d336960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335301 q = 0) : d336934 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335301, d336934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35083 q selected
    | true =>
      simp only [d335301, d336934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335302 q = 0) : d336935 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335302, d336935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335302, d336935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335303 q = 0) : d336936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335303, d336936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335303, d336936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335304 q = 0) : d336937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335304, d336937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335304, d336937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335305 q = 0) : d336938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335305, d336938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335305, d336938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335330 q = 0) : d336960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335330, d336960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335330, d336960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35094 (p : Pattern) (selected : d335336 p = 0) : d336966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335189 q = 0) : d336881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335189, d336881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35061 q selected
    | true =>
      simp only [d335189, d336881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35062 q selected
  have h2 (q : Pattern) (selected : d335190 q = 0) : d336882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335190, d336882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335190, d336882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335191 q = 0) : d336883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335191, d336883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335191, d336883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335192 q = 0) : d336884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335192, d336884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335192, d336884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335199 q = 0) : d336891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335199, d336891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35063 q selected
    | true =>
      simp only [d335199, d336891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35064 q selected
  have h6 (q : Pattern) (selected : d335200 q = 0) : d336892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335200, d336892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335200, d336892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335201 q = 0) : d336893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335201, d336893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335201, d336893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335218 q = 0) : d336910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335218, d336910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35067 q selected
    | true =>
      simp only [d335218, d336910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35055 q selected
  have h9 (q : Pattern) (selected : d335277 q = 0) : d336858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335277, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35077 q selected
    | true =>
      simp only [d335277, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35078 q selected
  have h10 (q : Pattern) (selected : d335278 q = 0) : d336911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335278, d336911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335278, d336911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335307 q = 0) : d336940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335307, d336940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35084 q selected
    | true =>
      simp only [d335307, d336940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335308 q = 0) : d336941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335308, d336941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335308, d336941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335309 q = 0) : d336942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335309, d336942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335309, d336942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335310 q = 0) : d336943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335310, d336943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335310, d336943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d335311 q = 0) : d336944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335311, d336944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335311, d336944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335315 q = 0) : d336948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335315, d336948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35086 q selected
    | true =>
      simp only [d335315, d336948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35087 q selected
  have h17 (q : Pattern) (selected : d335316 q = 0) : d336949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335316, d336949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335316, d336949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d335317 q = 0) : d336950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335317, d336950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d335317, d336950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d335318 q = 0) : d336951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335318, d336951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335318, d336951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d335321 q = 0) : d336954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335321, d336954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35088 q selected
    | true =>
      simp only [d335321, d336954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35089 q selected
  have h21 (q : Pattern) (selected : d335322 q = 0) : d336955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335322, d336955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335322, d336955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d335323 q = 0) : d336956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335323, d336956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d335323, d336956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d335325 q = 0) : d336958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335325, d336958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35090 q selected
    | true =>
      simp only [d335325, d336958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35058 q selected
  have h24 (q : Pattern) (selected : d335328 q = 0) : d336868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335328, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35091 q selected
    | true =>
      simp only [d335328, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35092 q selected
  have h25 (q : Pattern) (selected : d335329 q = 0) : d336959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335329, d336959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d335329, d336959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d335331 q = 0) : d336961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335331, d336961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35093 q selected
    | true =>
      simp only [d335331, d336961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d335332 q = 0) : d336962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335332, d336962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d335332, d336962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d335333 q = 0) : d336963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335333, d336963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d335333, d336963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d335334 q = 0) : d336964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335334, d336964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d335334, d336964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d335335 q = 0) : d336965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335335, d336965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335335, d336965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d335336 q = 0) : d336966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335336, d336966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335336, d336966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro35095 (p : Pattern) (selected : d335343 p = 0) : d336973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335166 q = 0) : d336858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35055 q selected
    | true =>
      simp only [d335166, d336858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35056 q selected
  have h2 (q : Pattern) (selected : d335167 q = 0) : d336859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335167, d336859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335168 q = 0) : d336860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335168, d336860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335169 q = 0) : d336861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335169, d336861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335170 q = 0) : d336862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335170, d336862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335338 q = 0) : d336968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335338, d336968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35056 q selected
    | true =>
      simp only [d335338, d336968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335339 q = 0) : d336969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335339, d336969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335339, d336969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335340 q = 0) : d336970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335340, d336970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335340, d336970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335341 q = 0) : d336971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335341, d336971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335341, d336971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335342 q = 0) : d336972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335342, d336972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335342, d336972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335343 q = 0) : d336973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335343, d336973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335343, d336973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35096 (p : Pattern) (selected : d335349 p = 0) : d336979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335338 q = 0) : d336968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335338, d336968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35056 q selected
    | true =>
      simp only [d335338, d336968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335339 q = 0) : d336969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335339, d336969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335339, d336969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335340 q = 0) : d336970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335340, d336970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335340, d336970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335341 q = 0) : d336971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335341, d336971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335341, d336971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335342 q = 0) : d336972 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335342, d336972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335342, d336972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335344 q = 0) : d336974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335344, d336974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35059 q selected
    | true =>
      simp only [d335344, d336974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335345 q = 0) : d336975 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335345, d336975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335345, d336975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335346 q = 0) : d336976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335346, d336976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335346, d336976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335347 q = 0) : d336977 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335347, d336977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335347, d336977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335348 q = 0) : d336978 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335348, d336978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335348, d336978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335349 q = 0) : d336979 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335349, d336979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335349, d336979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35097 (p : Pattern) (selected : d335356 p = 0) : d336986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335325 q = 0) : d336958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335325, d336958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35090 q selected
    | true =>
      simp only [d335325, d336958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35058 q selected
  have h2 (q : Pattern) (selected : d335328 q = 0) : d336868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335328, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35091 q selected
    | true =>
      simp only [d335328, d336868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35092 q selected
  have h3 (q : Pattern) (selected : d335329 q = 0) : d336959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335329, d336959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335329, d336959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335331 q = 0) : d336961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335331, d336961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35093 q selected
    | true =>
      simp only [d335331, d336961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335332 q = 0) : d336962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335332, d336962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335332, d336962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335333 q = 0) : d336963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335333, d336963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335333, d336963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335354 q = 0) : d336984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335354, d336984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335354, d336984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335355 q = 0) : d336985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335355, d336985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335355, d336985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335356 q = 0) : d336986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335356, d336986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335356, d336986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35098 (p : Pattern) (selected : d335358 p = 0) : d336988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335344 q = 0) : d336974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335344, d336974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35059 q selected
    | true =>
      simp only [d335344, d336974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335345 q = 0) : d336975 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335345, d336975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335345, d336975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335346 q = 0) : d336976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335346, d336976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335346, d336976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335347 q = 0) : d336977 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335347, d336977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335347, d336977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335348 q = 0) : d336978 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335348, d336978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335348, d336978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335358 q = 0) : d336988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335358, d336988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335358, d336988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35099 (p : Pattern) (selected : d335369 p = 0) : d336999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335364 q = 0) : d336994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
  have h2 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335365 q = 0) : d336995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335366 q = 0) : d336996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335367 q = 0) : d336997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335368 q = 0) : d336998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335368, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335368, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335369 q = 0) : d336999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335369, d336999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335369, d336999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35100 (p : Pattern) (selected : d335374 p = 0) : d337004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335364 q = 0) : d336994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
  have h2 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335365 q = 0) : d336995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335366 q = 0) : d336996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335367 q = 0) : d336997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335368 q = 0) : d336998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335368, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335368, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335373 q = 0) : d337003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335373, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335373, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335374 q = 0) : d337004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335374, d337004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335374, d337004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35101 (p : Pattern) (selected : d335388 p = 0) : d337018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335379 q = 0) : d337009 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335379, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335379, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
  have h2 (q : Pattern) (selected : d335122 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
    | true =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335380 q = 0) : d337010 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335380, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335380, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335123 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335381 q = 0) : d337011 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335381, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335381, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335382 q = 0) : d337012 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335382, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335382, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335383 q = 0) : d337013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
  have h8 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335384 q = 0) : d337014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335385 q = 0) : d337015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d335386 q = 0) : d337016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335387 q = 0) : d337017 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335387, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335387, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335364 q = 0) : d336994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335364, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
  have h15 (q : Pattern) (selected : d335112 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35046 q selected
    | true =>
      simp only [d335112, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335365 q = 0) : d336995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335365, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335113 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335113, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335366 q = 0) : d336996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335366, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335367 q = 0) : d336997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335367, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335373 q = 0) : d337003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335373, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335373, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335388 q = 0) : d337018 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335388, d337018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335388, d337018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35102 (p : Pattern) (selected : d335398 p = 0) : d337028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335383 q = 0) : d337013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
  have h2 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335384 q = 0) : d337014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335385 q = 0) : d337015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335386 q = 0) : d337016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335392 q = 0) : d337022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335392, d337022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335392, d337022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335393 q = 0) : d337023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335393, d337023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335393, d337023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35051 q selected
  have h9 (q : Pattern) (selected : d335139 q = 0) : d336831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335139, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35051 q selected
    | true =>
      simp only [d335139, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335394 q = 0) : d337024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335394, d337024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335394, d337024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335140 q = 0) : d336832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335140, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335140, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335395 q = 0) : d337025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335395, d337025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335395, d337025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335396 q = 0) : d337026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335396, d337026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335396, d337026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335397 q = 0) : d337027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335397, d337027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335397, d337027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335398 q = 0) : d337028 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335398, d337028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335398, d337028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35103 (p : Pattern) (selected : d335404 p = 0) : d337034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335370 q = 0) : d337000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335370, d337000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335370, d337000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35099 q selected
  have h2 (q : Pattern) (selected : d335371 q = 0) : d337001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335371, d337001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335371, d337001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335372 q = 0) : d337002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335372, d337002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335372, d337002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335375 q = 0) : d337005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335375, d337005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35099 q selected
    | true =>
      simp only [d335375, d337005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35100 q selected
  have h5 (q : Pattern) (selected : d335376 q = 0) : d337006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335376, d337006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335376, d337006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335377 q = 0) : d337007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335377, d337007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335377, d337007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335378 q = 0) : d337008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335378, d337008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335378, d337008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335389 q = 0) : d337019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35099 q selected
    | true =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
  have h9 (q : Pattern) (selected : d335390 q = 0) : d337020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335391 q = 0) : d337021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335399 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
    | true =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35102 q selected
  have h12 (q : Pattern) (selected : d335400 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335401 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335402 q = 0) : d337032 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d335403 q = 0) : d337033 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335403, d337033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335403, d337033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335404 q = 0) : d337034 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335404, d337034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335404, d337034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro35104 (p : Pattern) (selected : d335409 p = 0) : d337039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335389 q = 0) : d337019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35099 q selected
    | true =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
  have h2 (q : Pattern) (selected : d335390 q = 0) : d337020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335391 q = 0) : d337021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335399 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
    | true =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35102 q selected
  have h5 (q : Pattern) (selected : d335400 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335401 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335402 q = 0) : d337032 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335407 q = 0) : d337037 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335407, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335407, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335408 q = 0) : d337038 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335408, d337038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335408, d337038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335409 q = 0) : d337039 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335409, d337039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335409, d337039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35105 (p : Pattern) (selected : d335415 p = 0) : d337045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335405 q = 0) : d337035 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335405, d337035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35103 q selected
    | true =>
      simp only [d335405, d337035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335406 q = 0) : d337036 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335406, d337036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335406, d337036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335410 q = 0) : d337040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335410, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35104 q selected
    | true =>
      simp only [d335410, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335411 q = 0) : d337041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335411, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335411, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335412 q = 0) : d337042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335412, d337042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335412, d337042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335413 q = 0) : d337043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335413, d337043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335413, d337043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335414 q = 0) : d337044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335414, d337044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335414, d337044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335415 q = 0) : d337045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335415, d337045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335415, d337045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35106 (p : Pattern) (selected : d335417 p = 0) : d337047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335399 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
    | true =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35102 q selected
  have h2 (q : Pattern) (selected : d335400 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335401 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335407 q = 0) : d337037 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335407, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335407, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335416 q = 0) : d337046 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335416, d337046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335416, d337046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335417 q = 0) : d337047 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335417, d337047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335417, d337047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35107 (p : Pattern) (selected : d335423 p = 0) : d337053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335410 q = 0) : d337040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335410, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35104 q selected
    | true =>
      simp only [d335410, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335411 q = 0) : d337041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335411, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335411, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335418 q = 0) : d337048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335418, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35106 q selected
    | true =>
      simp only [d335418, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335419 q = 0) : d337049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335419, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335419, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335420 q = 0) : d337050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335420, d337050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335420, d337050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335421 q = 0) : d337051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335421, d337051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335421, d337051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335422 q = 0) : d337052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335422, d337052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335422, d337052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335423 q = 0) : d337053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335423, d337053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335423, d337053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35108 (p : Pattern) (selected : d335430 p = 0) : d336999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335425 q = 0) : d336994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335425, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335425, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
  have h2 (q : Pattern) (selected : d335223 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
    | true =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335426 q = 0) : d336995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335426, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335426, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335224 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335427 q = 0) : d336996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335427, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335427, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335428 q = 0) : d336997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335428, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335428, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335429 q = 0) : d336998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335429, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335429, d336998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335430 q = 0) : d336999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335430, d336999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335430, d336999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35109 (p : Pattern) (selected : d335441 p = 0) : d337018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335431 q = 0) : d337009 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335431, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335431, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35070 q selected
  have h2 (q : Pattern) (selected : d335233 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335233, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35070 q selected
    | true =>
      simp only [d335233, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335432 q = 0) : d337010 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335432, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335432, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335234 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335234, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335234, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335433 q = 0) : d337011 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335433, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335433, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335434 q = 0) : d337012 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335434, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335434, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335435 q = 0) : d337013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335435, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335435, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
  have h8 (q : Pattern) (selected : d335238 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
    | true =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335436 q = 0) : d337014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335436, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335436, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335239 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335437 q = 0) : d337015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335437, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335437, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d335438 q = 0) : d337016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335438, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335438, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335439 q = 0) : d337017 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335439, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335439, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335425 q = 0) : d336994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335425, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335425, d336994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
  have h15 (q : Pattern) (selected : d335223 q = 0) : d336804 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35068 q selected
    | true =>
      simp only [d335223, d336804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335426 q = 0) : d336995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335426, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335426, d336995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335224 q = 0) : d336805 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335224, d336805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335427 q = 0) : d336996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335427, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335427, d336996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335428 q = 0) : d336997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335428, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335428, d336997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335440 q = 0) : d337003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335440, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335440, d337003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335441 q = 0) : d337018 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335441, d337018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335441, d337018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35110 (p : Pattern) (selected : d335451 p = 0) : d337028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335435 q = 0) : d337013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335435, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335435, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
  have h2 (q : Pattern) (selected : d335238 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35071 q selected
    | true =>
      simp only [d335238, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335436 q = 0) : d337014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335436, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335436, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335239 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335239, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335437 q = 0) : d337015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335437, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335437, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335438 q = 0) : d337016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335438, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335438, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335445 q = 0) : d337022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335445, d337022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335445, d337022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335446 q = 0) : d337023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335446, d337023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335446, d337023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35073 q selected
  have h9 (q : Pattern) (selected : d335250 q = 0) : d336831 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335250, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35073 q selected
    | true =>
      simp only [d335250, d336831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335447 q = 0) : d337024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335447, d337024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335447, d337024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335251 q = 0) : d336832 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335251, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335251, d336832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335448 q = 0) : d337025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335448, d337025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335448, d337025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335449 q = 0) : d337026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335449, d337026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335449, d337026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335450 q = 0) : d337027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335450, d337027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335450, d337027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335451 q = 0) : d337028 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335451, d337028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335451, d337028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35111 (p : Pattern) (selected : d335458 p = 0) : d337039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335442 q = 0) : d337019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335442, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35108 q selected
    | true =>
      simp only [d335442, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35109 q selected
  have h2 (q : Pattern) (selected : d335443 q = 0) : d337020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335443, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335443, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335444 q = 0) : d337021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335444, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335444, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335452 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335452, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35109 q selected
    | true =>
      simp only [d335452, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35110 q selected
  have h5 (q : Pattern) (selected : d335453 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335453, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335453, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335454 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335454, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335454, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335455 q = 0) : d337032 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335455, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335455, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335456 q = 0) : d337037 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335456, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335456, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335457 q = 0) : d337038 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335457, d337038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335457, d337038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335458 q = 0) : d337039 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335458, d337039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335458, d337039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35112 (p : Pattern) (selected : d335462 p = 0) : d337047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335452 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335452, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35109 q selected
    | true =>
      simp only [d335452, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35110 q selected
  have h2 (q : Pattern) (selected : d335453 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335453, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335453, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335454 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335454, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335454, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335456 q = 0) : d337037 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335456, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335456, d337037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335461 q = 0) : d337046 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335461, d337046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335461, d337046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335462 q = 0) : d337047 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335462, d337047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335462, d337047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35113 (p : Pattern) (selected : d335468 p = 0) : d337053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335459 q = 0) : d337040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335459, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35111 q selected
    | true =>
      simp only [d335459, d337040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335460 q = 0) : d337041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335460, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335460, d337041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335463 q = 0) : d337048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335463, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35112 q selected
    | true =>
      simp only [d335463, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335464 q = 0) : d337049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335464, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335464, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335465 q = 0) : d337050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335465, d337050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335465, d337050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335466 q = 0) : d337051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335466, d337051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335466, d337051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335467 q = 0) : d337052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335467, d337052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335467, d337052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335468 q = 0) : d337053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335468, d337053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335468, d337053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35114 (p : Pattern) (selected : d335472 p = 0) : d337058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335463 q = 0) : d337048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335463, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35112 q selected
    | true =>
      simp only [d335463, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335464 q = 0) : d337049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335464, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335464, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335469 q = 0) : d337055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335469, d337055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335469, d337055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335470 q = 0) : d337056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335470, d337056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335470, d337056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335471 q = 0) : d337057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335471, d337057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335471, d337057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335472 q = 0) : d337058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335472, d337058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335472, d337058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35115 (p : Pattern) (selected : d335480 p = 0) : d337066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335379 q = 0) : d337009 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335379, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335379, d337009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
  have h2 (q : Pattern) (selected : d335122 q = 0) : d336814 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35048 q selected
    | true =>
      simp only [d335122, d336814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335380 q = 0) : d337010 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335380, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335380, d337010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335123 q = 0) : d336815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335123, d336815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335381 q = 0) : d337011 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335381, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335381, d337011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335382 q = 0) : d337012 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335382, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335382, d337012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335383 q = 0) : d337013 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335383, d337013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
  have h8 (q : Pattern) (selected : d335127 q = 0) : d336819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35049 q selected
    | true =>
      simp only [d335127, d336819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335384 q = 0) : d337014 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335384, d337014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335128 q = 0) : d336820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335128, d336820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335385 q = 0) : d337015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335385, d337015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d335386 q = 0) : d337016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335386, d337016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335387 q = 0) : d337017 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335387, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335387, d337017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335475 q = 0) : d337061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335475, d337061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335475, d337061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35079 q selected
  have h15 (q : Pattern) (selected : d335282 q = 0) : d336915 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335282, d336915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35079 q selected
    | true =>
      simp only [d335282, d336915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335476 q = 0) : d337062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335476, d337062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335476, d337062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335283 q = 0) : d336916 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335283, d336916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335283, d336916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335477 q = 0) : d337063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335477, d337063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335477, d337063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335478 q = 0) : d337064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335478, d337064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335478, d337064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335479 q = 0) : d337065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335479, d337065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335479, d337065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335480 q = 0) : d337066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335480, d337066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335480, d337066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35116 (p : Pattern) (selected : d335486 p = 0) : d337072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335481 q = 0) : d337067 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335481, d337067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335481, d337067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35081 q selected
  have h2 (q : Pattern) (selected : d335289 q = 0) : d336922 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335289, d336922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35081 q selected
    | true =>
      simp only [d335289, d336922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335482 q = 0) : d337068 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335482, d337068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335482, d337068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335290 q = 0) : d336923 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335290, d336923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335290, d336923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335483 q = 0) : d337069 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335483, d337069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335483, d337069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335484 q = 0) : d337070 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335484, d337070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335484, d337070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335485 q = 0) : d337071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335485, d337071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335485, d337071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335486 q = 0) : d337072 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335486, d337072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335486, d337072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35117 (p : Pattern) (selected : d335492 p = 0) : d337078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335389 q = 0) : d337019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35099 q selected
    | true =>
      simp only [d335389, d337019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
  have h2 (q : Pattern) (selected : d335390 q = 0) : d337020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335390, d337020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335391 q = 0) : d337021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335391, d337021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335399 q = 0) : d337029 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35101 q selected
    | true =>
      simp only [d335399, d337029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35102 q selected
  have h5 (q : Pattern) (selected : d335400 q = 0) : d337030 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335400, d337030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335401 q = 0) : d337031 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335401, d337031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335402 q = 0) : d337032 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335402, d337032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335487 q = 0) : d337073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335487, d337073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35115 q selected
    | true =>
      simp only [d335487, d337073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35116 q selected
  have h9 (q : Pattern) (selected : d335488 q = 0) : d337074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335488, d337074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335488, d337074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335489 q = 0) : d337075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335489, d337075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335489, d337075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335490 q = 0) : d337076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335490, d337076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335490, d337076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335491 q = 0) : d337077 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335491, d337077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335491, d337077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335492 q = 0) : d337078 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335492, d337078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335492, d337078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro35118 (p : Pattern) (selected : d335498 p = 0) : d337084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335493 q = 0) : d337079 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335493, d337079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35117 q selected
    | true =>
      simp only [d335493, d337079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335494 q = 0) : d337080 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335494, d337080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335494, d337080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335495 q = 0) : d337081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335495, d337081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335495, d337081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335496 q = 0) : d337082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335496, d337082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335496, d337082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335497 q = 0) : d337083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335497, d337083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335497, d337083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335498 q = 0) : d337084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335498, d337084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335498, d337084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35119 (p : Pattern) (selected : d335504 p = 0) : d337090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335424 q = 0) : d337054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335424, d337054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35105 q selected
    | true =>
      simp only [d335424, d337054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35107 q selected
  have h2 (q : Pattern) (selected : d335473 q = 0) : d337059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335473, d337059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35113 q selected
    | true =>
      simp only [d335473, d337059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35114 q selected
  have h3 (q : Pattern) (selected : d335474 q = 0) : d337060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335474, d337060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335474, d337060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335499 q = 0) : d337085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335499, d337085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35118 q selected
    | true =>
      simp only [d335499, d337085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335500 q = 0) : d337086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335500, d337086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335500, d337086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335501 q = 0) : d337087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335501, d337087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335501, d337087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335502 q = 0) : d337088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335502, d337088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335502, d337088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335503 q = 0) : d337089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335503, d337089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335503, d337089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335504 q = 0) : d337090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335504, d337090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335504, d337090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro35120 (p : Pattern) (selected : d335509 p = 0) : d337058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335418 q = 0) : d337048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335418, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35106 q selected
    | true =>
      simp only [d335418, d337048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335419 q = 0) : d337049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335419, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335419, d337049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335506 q = 0) : d337055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335506, d337055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335506, d337055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335507 q = 0) : d337056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335507, d337056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335507, d337056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335508 q = 0) : d337057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335508, d337057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335508, d337057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335509 q = 0) : d337058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335509, d337058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335509, d337058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35121 (p : Pattern) (selected : d335515 p = 0) : d337097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335510 q = 0) : d337092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335510, d337092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35120 q selected
    | true =>
      simp only [d335510, d337092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335511 q = 0) : d337093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335511, d337093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335511, d337093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335512 q = 0) : d337094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335512, d337094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335512, d337094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335513 q = 0) : d337095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335513, d337095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335513, d337095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335514 q = 0) : d337096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335514, d337096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335514, d337096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335515 q = 0) : d337097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335515, d337097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335515, d337097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35122 (p : Pattern) (selected : d335521 p = 0) : d337103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335172 q = 0) : d336864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335172, d336864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335172, d336864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35057 q selected
  have h2 (q : Pattern) (selected : d335173 q = 0) : d336865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335173, d336865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335173, d336865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335182 q = 0) : d336874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335182, d336874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35057 q selected
    | true =>
      simp only [d335182, d336874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35060 q selected
  have h4 (q : Pattern) (selected : d335183 q = 0) : d336875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335183, d336875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335183, d336875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335184 q = 0) : d336876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335184, d336876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335184, d336876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335337 q = 0) : d336967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335337, d336967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35085 q selected
    | true =>
      simp only [d335337, d336967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35094 q selected
  have h7 (q : Pattern) (selected : d335350 q = 0) : d336980 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335350, d336980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35095 q selected
    | true =>
      simp only [d335350, d336980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35096 q selected
  have h8 (q : Pattern) (selected : d335351 q = 0) : d336981 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335351, d336981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335351, d336981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335352 q = 0) : d336982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335352, d336982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335352, d336982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335353 q = 0) : d336983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d335353, d336983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335353, d336983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335357 q = 0) : d336987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335357, d336987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335357, d336987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35097 q selected
  have h12 (q : Pattern) (selected : d335359 q = 0) : d336989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335359, d336989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335359, d336989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35098 q selected
  have h13 (q : Pattern) (selected : d335360 q = 0) : d336990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335360, d336990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335360, d336990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335361 q = 0) : d336991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335361, d336991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335361, d336991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335362 q = 0) : d336992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d335362, d336992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335362, d336992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335363 q = 0) : d336993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d335363, d336993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335363, d336993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335505 q = 0) : d337091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335505, d337091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335505, d337091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35119 q selected
  have h18 (q : Pattern) (selected : d335516 q = 0) : d337098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335516, d337098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335516, d337098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35121 q selected
  have h19 (q : Pattern) (selected : d335517 q = 0) : d337099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335517, d337099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d335517, d337099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d335518 q = 0) : d337100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335518, d337100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335518, d337100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335519 q = 0) : d337101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d335519, d337101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d335519, d337101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d335520 q = 0) : d337102 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d335520, d337102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d335520, d337102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d335521 q = 0) : d337103 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d335521, d337103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335521, d337103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro35123 (p : Pattern) (selected : d335527 p = 0) : d337109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335522 q = 0) : d337104 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d335522, d337104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335522, d337104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35122 q selected
  have h2 (q : Pattern) (selected : d335523 q = 0) : d337105 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d335523, d337105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335523, d337105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335524 q = 0) : d337106 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d335524, d337106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335524, d337106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335525 q = 0) : d337107 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d335525, d337107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335525, d337107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335526 q = 0) : d337108 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d335526, d337108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335526, d337108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335527 q = 0) : d337109 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d335527, d337109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335527, d337109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35124 (p : Pattern) (selected : d335533 p = 0) : d337115 p = 1 := by
  have h0 (q : Pattern) (selected : d333923 q = 0) : d335936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d333923, d335936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34790 q selected
    | true =>
      simp only [d333923, d335936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34825 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d334247 q = 0) : d336179 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d334247, d336179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334247, d336179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34889 q selected
  have h3 (q : Pattern) (selected : d334248 q = 0) : d336180 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d334248, d336180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334248, d336180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334627 q = 0) : d336456 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d334627, d336456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334627, d336456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34963 q selected
  have h5 (q : Pattern) (selected : d334628 q = 0) : d336457 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d334628, d336457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334628, d336457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334629 q = 0) : d336458 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d334629, d336458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334629, d336458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335104 q = 0) : d336796 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d335104, d336796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335104, d336796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35045 q selected
  have h8 (q : Pattern) (selected : d335105 q = 0) : d336797 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d335105, d336797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335105, d336797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335106 q = 0) : d336798 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d335106, d336798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335106, d336798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335107 q = 0) : d336799 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d335107, d336799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335107, d336799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d335528 q = 0) : d337110 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d335528, d337110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335528, d337110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35123 q selected
  have h12 (q : Pattern) (selected : d335529 q = 0) : d337111 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d335529, d337111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335529, d337111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335530 q = 0) : d337112 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d335530, d337112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335530, d337112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335531 q = 0) : d337113 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d335531, d337113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335531, d337113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d335532 q = 0) : d337114 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d335532, d337114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335532, d337114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335533 q = 0) : d337115 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d335533, d337115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335533, d337115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro35125 (p : Pattern) (selected : d335539 p = 0) : d337121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335534 q = 0) : d337116 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d335534, d337116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35124 q selected
    | true =>
      simp only [d335534, d337116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335535 q = 0) : d337117 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d335535, d337117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335535, d337117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335536 q = 0) : d337118 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d335536, d337118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335536, d337118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335537 q = 0) : d337119 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d335537, d337119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335537, d337119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335538 q = 0) : d337120 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d335538, d337120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335538, d337120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335539 q = 0) : d337121 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d335539, d337121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335539, d337121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35126 (p : Pattern) (selected : d335545 p = 0) : d337127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335540 q = 0) : d337122 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d335540, d337122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35125 q selected
    | true =>
      simp only [d335540, d337122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335541 q = 0) : d337123 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d335541, d337123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335541, d337123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335542 q = 0) : d337124 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d335542, d337124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335542, d337124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335543 q = 0) : d337125 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d335543, d337125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335543, d337125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335544 q = 0) : d337126 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d335544, d337126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335544, d337126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335545 q = 0) : d337127 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d335545, d337127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335545, d337127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35127 (p : Pattern) (selected : d335551 p = 0) : d337133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335546 q = 0) : d337128 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d335546, d337128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35126 q selected
    | true =>
      simp only [d335546, d337128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335547 q = 0) : d337129 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d335547, d337129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335547, d337129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335548 q = 0) : d337130 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d335548, d337130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335548, d337130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335549 q = 0) : d337131 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d335549, d337131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335549, d337131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335550 q = 0) : d337132 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d335550, d337132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335550, d337132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335551 q = 0) : d337133 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d335551, d337133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335551, d337133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35128 (p : Pattern) (selected : d335557 p = 0) : d337139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335552 q = 0) : d337134 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d335552, d337134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35127 q selected
    | true =>
      simp only [d335552, d337134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335553 q = 0) : d337135 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d335553, d337135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335553, d337135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335554 q = 0) : d337136 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d335554, d337136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335554, d337136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335555 q = 0) : d337137 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d335555, d337137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335555, d337137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335556 q = 0) : d337138 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d335556, d337138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335556, d337138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335557 q = 0) : d337139 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d335557, d337139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335557, d337139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35129 (p : Pattern) (selected : d335563 p = 0) : d337145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335558 q = 0) : d337140 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d335558, d337140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35128 q selected
    | true =>
      simp only [d335558, d337140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335559 q = 0) : d337141 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d335559, d337141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335559, d337141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335560 q = 0) : d337142 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d335560, d337142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335560, d337142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335561 q = 0) : d337143 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d335561, d337143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335561, d337143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335562 q = 0) : d337144 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d335562, d337144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335562, d337144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335563 q = 0) : d337145 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d335563, d337145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335563, d337145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35130 (p : Pattern) (selected : d335569 p = 0) : d337151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335564 q = 0) : d337146 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d335564, d337146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35129 q selected
    | true =>
      simp only [d335564, d337146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335565 q = 0) : d337147 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d335565, d337147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335565, d337147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335566 q = 0) : d337148 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d335566, d337148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335566, d337148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335567 q = 0) : d337149 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d335567, d337149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335567, d337149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335568 q = 0) : d337150 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d335568, d337150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335568, d337150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335569 q = 0) : d337151 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d335569, d337151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335569, d337151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35131 (p : Pattern) (selected : d335575 p = 0) : d337157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d335570 q = 0) : d337152 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d335570, d337152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35130 q selected
    | true =>
      simp only [d335570, d337152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335571 q = 0) : d337153 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d335571, d337153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335571, d337153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335572 q = 0) : d337154 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d335572, d337154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335572, d337154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335573 q = 0) : d337155 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d335573, d337155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335573, d337155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335574 q = 0) : d337156 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d335574, d337156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335574, d337156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335575 q = 0) : d337157 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d335575, d337157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335575, d337157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35132 (p : Pattern) (selected : d333608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333607 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333608 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro35133 (p : Pattern) (selected : d333614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333613 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333614 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35134 (p : Pattern) (selected : d333620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35133 q selected
    | true =>
      simp only [d333615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333619 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333620 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35135 (p : Pattern) (selected : d333626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35134 q selected
    | true =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333623 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333624 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333625 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333626 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35136 (p : Pattern) (selected : d333632 p = 1) : d338259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333575 q = 1) : d333575 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333581 q = 1) : d333581 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d333604 q = 1) : d333604 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d333627 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35135 q selected
    | true =>
      simp only [d333627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333628 q = 1) : d338255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333628, d338255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333628, d338255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333498 q = 1) : d333498 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d333629 q = 1) : d338256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333629, d338256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333629, d338256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333630 q = 1) : d338257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333630, d338257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333630, d338257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333631 q = 1) : d338258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333631, d338258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333631, d338258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333632 q = 1) : d338259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333632, d338259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333632, d338259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35137 (p : Pattern) (selected : d333644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35134 q selected
    | true =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333623 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333624 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333625 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333644 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35138 (p : Pattern) (selected : d333650 p = 1) : d338264 p = 1 := by
  have h0 (q : Pattern) (selected : d333575 q = 1) : d333575 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333581 q = 1) : d333581 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333604 q = 1) : d333604 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d333627 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35135 q selected
    | true =>
      simp only [d333627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333628 q = 1) : d338255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333628, d338255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333628, d338255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333498 q = 1) : d333498 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d333629 q = 1) : d338256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333629, d338256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333629, d338256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333630 q = 1) : d338257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333630, d338257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333630, d338257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333631 q = 1) : d338258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333631, d338258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333631, d338258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333637 q = 1) : d333637 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d333641 q = 1) : d333641 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d333643 q = 1) : d333643 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d333645 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35137 q selected
    | true =>
      simp only [d333645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d333646 q = 1) : d338260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333646, d338260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333646, d338260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333505 q = 1) : d333505 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d333647 q = 1) : d338261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333647, d338261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333647, d338261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333648 q = 1) : d338262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333648, d338262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333648, d338262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d333649 q = 1) : d338263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333649, d338263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333649, d338263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d333650 q = 1) : d338264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333650, d338264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333650, d338264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro35139 (p : Pattern) (selected : d333659 p = 1) : d338271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333643 q = 1) : d333643 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333645 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35137 q selected
    | true =>
      simp only [d333645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333646 q = 1) : d338260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333646, d338260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333646, d338260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333505 q = 1) : d333505 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333647 q = 1) : d338261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333647, d338261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333647, d338261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333657 q = 1) : d338269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333657, d338269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333657, d338269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333658 q = 1) : d338270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333658, d338270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333658, d338270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333659 q = 1) : d338271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333659, d338271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333659, d338271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35140 (p : Pattern) (selected : d333689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
  have h2 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333689 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35141 (p : Pattern) (selected : d333695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333690 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35140 q selected
    | true =>
      simp only [d333690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333691 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333694 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333695 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35142 (p : Pattern) (selected : d333701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333696 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35141 q selected
    | true =>
      simp only [d333696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333697 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35143 (p : Pattern) (selected : d333707 p = 1) : d338281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333683 q = 1) : d333683 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35142 q selected
    | true =>
      simp only [d333702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333703 q = 1) : d338277 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333703, d338277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333703, d338277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333539 q = 1) : d333539 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333704 q = 1) : d338278 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333704, d338278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333704, d338278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333705 q = 1) : d338279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333705, d338279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333705, d338279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333706 q = 1) : d338280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333706, d338280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333706, d338280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333707 q = 1) : d338281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333707, d338281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333707, d338281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35144 (p : Pattern) (selected : d333713 p = 1) : d338287 p = 1 := by
  have h0 (q : Pattern) (selected : d333569 q = 1) : d333569 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333651 q = 1) : d338265 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333651, d338265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35136 q selected
    | true =>
      simp only [d333651, d338265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35138 q selected
  have h2 (q : Pattern) (selected : d333653 q = 1) : d333653 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d333654 q = 1) : d338266 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333654, d338266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333654, d338266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333655 q = 1) : d338267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333655, d338267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333655, d338267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333656 q = 1) : d338268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333656, d338268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333656, d338268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333660 q = 1) : d338272 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333660, d338272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333660, d338272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35139 q selected
  have h8 (q : Pattern) (selected : d333661 q = 1) : d338273 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333661, d338273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333661, d338273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d333662 q = 1) : d338274 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333662, d338274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333662, d338274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d333663 q = 1) : d338275 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333663, d338275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333663, d338275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d333664 q = 1) : d338276 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333664, d338276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333664, d338276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333708 q = 1) : d338282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333708, d338282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333708, d338282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35143 q selected
  have h13 (q : Pattern) (selected : d333709 q = 1) : d338283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333709, d338283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333709, d338283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d333710 q = 1) : d338284 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333710, d338284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333710, d338284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d333711 q = 1) : d338285 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333711, d338285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333711, d338285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d333712 q = 1) : d338286 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333712, d338286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333712, d338286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d333713 q = 1) : d338287 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333713, d338287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333713, d338287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro35145 (p : Pattern) (selected : d333719 p = 1) : d338293 p = 1 := by
  have h0 (q : Pattern) (selected : d333554 q = 1) : d333554 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333714 q = 1) : d338288 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333714, d338288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333714, d338288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35144 q selected
  have h3 (q : Pattern) (selected : d333715 q = 1) : d338289 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333715, d338289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333715, d338289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333716 q = 1) : d338290 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333716, d338290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333716, d338290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333717 q = 1) : d338291 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333717, d338291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333717, d338291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333718 q = 1) : d338292 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333718, d338292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333718, d338292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333719 q = 1) : d338293 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333719, d338293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333719, d338293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35146 (p : Pattern) (selected : d333781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333779 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333780 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333607 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333781 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35147 (p : Pattern) (selected : d333787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333786 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333787 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35148 (p : Pattern) (selected : d333793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333788 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35147 q selected
    | true =>
      simp only [d333788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35133 q selected
  have h2 (q : Pattern) (selected : d333789 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333790 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35133 q selected
    | true =>
      simp only [d333615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333791 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333792 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333793 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35149 (p : Pattern) (selected : d333799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35148 q selected
    | true =>
      simp only [d333794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35134 q selected
    | true =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333799 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35150 (p : Pattern) (selected : d333811 p = 1) : d338298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333740 q = 1) : d333740 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333746 q = 1) : d333746 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d333777 q = 1) : d333777 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d333800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35149 q selected
    | true =>
      simp only [d333800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35135 q selected
  have h5 (q : Pattern) (selected : d333801 q = 1) : d338294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333801, d338294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333801, d338294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333807 q = 1) : d333807 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d333808 q = 1) : d338295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333808, d338295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333808, d338295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333809 q = 1) : d338296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333809, d338296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333809, d338296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333810 q = 1) : d338297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333810, d338297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333810, d338297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333811 q = 1) : d338298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333811, d338298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333811, d338298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35151 (p : Pattern) (selected : d333823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35148 q selected
    | true =>
      simp only [d333794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35134 q selected
    | true =>
      simp only [d333621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35152 (p : Pattern) (selected : d333832 p = 1) : d338303 p = 1 := by
  have h0 (q : Pattern) (selected : d333740 q = 1) : d333740 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333746 q = 1) : d333746 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333777 q = 1) : d333777 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d333800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35149 q selected
    | true =>
      simp only [d333800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35135 q selected
  have h4 (q : Pattern) (selected : d333801 q = 1) : d338294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333801, d338294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333801, d338294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333807 q = 1) : d333807 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d333808 q = 1) : d338295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333808, d338295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333808, d338295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333809 q = 1) : d338296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333809, d338296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333809, d338296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333810 q = 1) : d338297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333810, d338297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333810, d338297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333816 q = 1) : d333816 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d333820 q = 1) : d333820 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d333822 q = 1) : d333822 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d333824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35151 q selected
    | true =>
      simp only [d333824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35137 q selected
  have h13 (q : Pattern) (selected : d333825 q = 1) : d338299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333825, d338299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333825, d338299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333828 q = 1) : d333828 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d333829 q = 1) : d338300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333829, d338300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333829, d338300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333830 q = 1) : d338301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333830, d338301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333830, d338301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333831 q = 1) : d338302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333831, d338302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333831, d338302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d333832 q = 1) : d338303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333832, d338303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333832, d338303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro35153 (p : Pattern) (selected : d333841 p = 1) : d338310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333822 q = 1) : d333822 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35151 q selected
    | true =>
      simp only [d333824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35137 q selected
  have h3 (q : Pattern) (selected : d333825 q = 1) : d338299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333825, d338299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333825, d338299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333828 q = 1) : d333828 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333829 q = 1) : d338300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333829, d338300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333829, d338300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333839 q = 1) : d338308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333839, d338308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333839, d338308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333840 q = 1) : d338309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333840, d338309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333840, d338309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333841 q = 1) : d338310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333841, d338310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333841, d338310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35154 (p : Pattern) (selected : d333880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
  have h2 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
  have h8 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333879 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333880 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro35155 (p : Pattern) (selected : d333886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333881 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35154 q selected
    | true =>
      simp only [d333881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35140 q selected
  have h2 (q : Pattern) (selected : d333882 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333883 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333690 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35140 q selected
    | true =>
      simp only [d333690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333691 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333884 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333885 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333886 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35156 (p : Pattern) (selected : d333892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333887 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35155 q selected
    | true =>
      simp only [d333887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333888 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333696 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35141 q selected
    | true =>
      simp only [d333696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333697 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333889 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333890 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35157 (p : Pattern) (selected : d333904 p = 1) : d338320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333874 q = 1) : d333874 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35156 q selected
    | true =>
      simp only [d333893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35142 q selected
  have h3 (q : Pattern) (selected : d333894 q = 1) : d338316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333894, d338316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333894, d338316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333900 q = 1) : d333900 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333901 q = 1) : d338317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333901, d338317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333901, d338317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333902 q = 1) : d338318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333902, d338318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333902, d338318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333903 q = 1) : d338319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333903, d338319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333903, d338319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333904 q = 1) : d338320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333904, d338320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333904, d338320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35158 (p : Pattern) (selected : d333916 p = 1) : d338326 p = 1 := by
  have h0 (q : Pattern) (selected : d333734 q = 1) : d333734 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333833 q = 1) : d338304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333833, d338304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35150 q selected
    | true =>
      simp only [d333833, d338304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35152 q selected
  have h2 (q : Pattern) (selected : d333835 q = 1) : d333835 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d333836 q = 1) : d338305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333836, d338305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333836, d338305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d333837 q = 1) : d338306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333837, d338306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333837, d338306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333838 q = 1) : d338307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333838, d338307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333838, d338307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333842 q = 1) : d338311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333842, d338311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333842, d338311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35153 q selected
  have h8 (q : Pattern) (selected : d333844 q = 1) : d333844 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d333845 q = 1) : d338312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333845, d338312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333845, d338312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333846 q = 1) : d338313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333846, d338313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333846, d338313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d333847 q = 1) : d338314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333847, d338314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333847, d338314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d333848 q = 1) : d338315 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333848, d338315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333848, d338315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333905 q = 1) : d338321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333905, d338321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333905, d338321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35157 q selected
  have h14 (q : Pattern) (selected : d333911 q = 1) : d333911 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d333912 q = 1) : d338322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333912, d338322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333912, d338322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333913 q = 1) : d338323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333913, d338323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333913, d338323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d333914 q = 1) : d338324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333914, d338324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333914, d338324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d333915 q = 1) : d338325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333915, d338325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d333915, d338325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d333916 q = 1) : d338326 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333916, d338326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333916, d338326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro35159 (p : Pattern) (selected : d333922 p = 1) : d338332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333917 q = 1) : d338327 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333917, d338327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333917, d338327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35158 q selected
  have h2 (q : Pattern) (selected : d333918 q = 1) : d338328 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333918, d338328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333918, d338328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333919 q = 1) : d338329 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333919, d338329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333919, d338329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333920 q = 1) : d338330 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333920, d338330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333920, d338330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333921 q = 1) : d338331 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333921, d338331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333921, d338331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333922 q = 1) : d338332 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333922, d338332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333922, d338332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35160 (p : Pattern) (selected : d334025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334022 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23824 q selected
    | true =>
      simp only [d334022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334023 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334024 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333779 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333780 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334025 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35161 (p : Pattern) (selected : d334030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333779 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333780 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334030 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro35162 (p : Pattern) (selected : d334037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
    | true =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35161 q selected
    | true =>
      simp only [d334031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334036 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334037 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35163 (p : Pattern) (selected : d334038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333786 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333613 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334038 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35164 (p : Pattern) (selected : d334048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35162 q selected
    | true =>
      simp only [d334039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35163 q selected
  have h2 (q : Pattern) (selected : d334040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334042 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35163 q selected
    | true =>
      simp only [d334042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35133 q selected
  have h5 (q : Pattern) (selected : d334043 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334044 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334045 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334047 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334048 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35165 (p : Pattern) (selected : d334052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334042 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35163 q selected
    | true =>
      simp only [d334042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35133 q selected
  have h2 (q : Pattern) (selected : d334043 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334044 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334051 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334052 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35166 (p : Pattern) (selected : d334058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35164 q selected
    | true =>
      simp only [d334049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334053 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35165 q selected
    | true =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334054 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334055 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334056 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334057 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35167 (p : Pattern) (selected : d334062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334053 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35165 q selected
    | true =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334054 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334062 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35168 (p : Pattern) (selected : d334074 p = 1) : d338338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333977 q = 1) : d333977 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d333986 q = 1) : d333986 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334021 q = 1) : d334021 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d334063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35166 q selected
    | true =>
      simp only [d334063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35167 q selected
  have h5 (q : Pattern) (selected : d334064 q = 1) : d338334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334064, d338334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334064, d338334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334070 q = 1) : d334070 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d334071 q = 1) : d338335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334071, d338335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334071, d338335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334072 q = 1) : d338336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334072, d338336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334072, d338336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334073 q = 1) : d338337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334073, d338337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334073, d338337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334074 q = 1) : d338338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334074, d338338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334074, d338338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35169 (p : Pattern) (selected : d334088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35164 q selected
    | true =>
      simp only [d334049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334053 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35165 q selected
    | true =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334054 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334055 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334056 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334057 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35170 (p : Pattern) (selected : d334089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334053 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35165 q selected
    | true =>
      simp only [d334053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334054 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334059 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334060 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334061 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35171 (p : Pattern) (selected : d334098 p = 1) : d338343 p = 1 := by
  have h0 (q : Pattern) (selected : d333977 q = 1) : d333977 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333986 q = 1) : d333986 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334021 q = 1) : d334021 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334063 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35166 q selected
    | true =>
      simp only [d334063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35167 q selected
  have h4 (q : Pattern) (selected : d334064 q = 1) : d338334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334064, d338334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334064, d338334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334070 q = 1) : d334070 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d334071 q = 1) : d338335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334071, d338335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334071, d338335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334072 q = 1) : d338336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334072, d338336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334072, d338336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334073 q = 1) : d338337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334073, d338337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334073, d338337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334080 q = 1) : d334080 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d334085 q = 1) : d334085 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d334087 q = 1) : d334087 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d334090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35169 q selected
    | true =>
      simp only [d334090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35170 q selected
  have h13 (q : Pattern) (selected : d334091 q = 1) : d338339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334091, d338339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334091, d338339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334094 q = 1) : d334094 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d334095 q = 1) : d338340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334095, d338340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334095, d338340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334096 q = 1) : d338341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334096, d338341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334096, d338341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334097 q = 1) : d338342 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334097, d338342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334097, d338342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334098 q = 1) : d338343 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334098, d338343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334098, d338343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro35172 (p : Pattern) (selected : d334118 p = 1) : d338350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334087 q = 1) : d334087 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35169 q selected
    | true =>
      simp only [d334090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35170 q selected
  have h3 (q : Pattern) (selected : d334091 q = 1) : d338339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334091, d338339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334091, d338339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334094 q = 1) : d334094 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334095 q = 1) : d338340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334095, d338340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334095, d338340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334116 q = 1) : d338348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334116, d338348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334116, d338348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334117 q = 1) : d338349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334117, d338349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334117, d338349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334118 q = 1) : d338350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334118, d338350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334118, d338350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35173 (p : Pattern) (selected : d334186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334176 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
  have h2 (q : Pattern) (selected : d334026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
    | true =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334177 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334178 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334179 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35161 q selected
  have h8 (q : Pattern) (selected : d334031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35161 q selected
    | true =>
      simp only [d334031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
  have h15 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d333685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d333686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d333687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334185 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334186 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35174 (p : Pattern) (selected : d334187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
  have h2 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
  have h8 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333879 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334187 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35175 (p : Pattern) (selected : d334197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334188 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35173 q selected
    | true =>
      simp only [d334188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35174 q selected
  have h2 (q : Pattern) (selected : d334189 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334190 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35174 q selected
    | true =>
      simp only [d334191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35140 q selected
  have h5 (q : Pattern) (selected : d334192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334195 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334196 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334197 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35176 (p : Pattern) (selected : d334201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35174 q selected
    | true =>
      simp only [d334191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35140 q selected
  have h2 (q : Pattern) (selected : d334192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334195 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334200 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334201 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35177 (p : Pattern) (selected : d334207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334198 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35175 q selected
    | true =>
      simp only [d334198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334199 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334202 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35176 q selected
    | true =>
      simp only [d334202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334203 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334204 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334205 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334206 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35178 (p : Pattern) (selected : d334211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334202 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35176 q selected
    | true =>
      simp only [d334202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334203 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334208 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334209 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35179 (p : Pattern) (selected : d334223 p = 1) : d338360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334175 q = 1) : d334175 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35177 q selected
    | true =>
      simp only [d334212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35178 q selected
  have h3 (q : Pattern) (selected : d334213 q = 1) : d338356 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334213, d338356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334213, d338356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334219 q = 1) : d334219 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334220 q = 1) : d338357 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334220, d338357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334220, d338357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334221 q = 1) : d338358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334221, d338358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334221, d338358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334222 q = 1) : d338359 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334222, d338359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334222, d338359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334223 q = 1) : d338360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334223, d338360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334223, d338360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35180 (p : Pattern) (selected : d334240 p = 1) : d338366 p = 1 := by
  have h0 (q : Pattern) (selected : d333969 q = 1) : d333969 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334099 q = 1) : d338344 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334099, d338344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35168 q selected
    | true =>
      simp only [d334099, d338344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35171 q selected
  have h2 (q : Pattern) (selected : d334112 q = 1) : d334112 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334113 q = 1) : d338345 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334113, d338345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334113, d338345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334114 q = 1) : d338346 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334114, d338346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334114, d338346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334115 q = 1) : d338347 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334115, d338347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334115, d338347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334119 q = 1) : d338351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334119, d338351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334119, d338351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35172 q selected
  have h8 (q : Pattern) (selected : d334121 q = 1) : d334121 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d334122 q = 1) : d338352 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334122, d338352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334122, d338352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334123 q = 1) : d338353 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334123, d338353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334123, d338353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d334124 q = 1) : d338354 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334124, d338354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334124, d338354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d334125 q = 1) : d338355 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334125, d338355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334125, d338355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334224 q = 1) : d338361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334224, d338361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334224, d338361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35179 q selected
  have h14 (q : Pattern) (selected : d334235 q = 1) : d334235 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d334236 q = 1) : d338362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334236, d338362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334236, d338362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334237 q = 1) : d338363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334237, d338363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334237, d338363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d334238 q = 1) : d338364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334238, d338364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334238, d338364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d334239 q = 1) : d338365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334239, d338365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334239, d338365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d334240 q = 1) : d338366 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d334240, d338366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334240, d338366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro35181 (p : Pattern) (selected : d334246 p = 1) : d338372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334241 q = 1) : d338367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d334241, d338367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334241, d338367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35180 q selected
  have h2 (q : Pattern) (selected : d334242 q = 1) : d338368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d334242, d338368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334242, d338368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334243 q = 1) : d338369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d334243, d338369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334243, d338369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334244 q = 1) : d338370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d334244, d338370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334244, d338370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334245 q = 1) : d338371 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d334245, d338371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334245, d338371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334246 q = 1) : d338372 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d334246, d338372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334246, d338372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35182 (p : Pattern) (selected : d334360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334354 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23840 q selected
    | true =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334355 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23841 q selected
    | true =>
      simp only [d334355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334356 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334357 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334358 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334359 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334360 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35183 (p : Pattern) (selected : d334365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334022 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23824 q selected
    | true =>
      simp only [d334022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334023 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334024 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334365 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro35184 (p : Pattern) (selected : d334373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d333778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334371 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334372 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333605 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d333605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333606 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333607 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334373 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35185 (p : Pattern) (selected : d334379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35182 q selected
    | true =>
      simp only [d334361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35183 q selected
    | true =>
      simp only [d334366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334368 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334369 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334370 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
    | true =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334376 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334377 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334378 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334379 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35186 (p : Pattern) (selected : d334382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
    | true =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
    | true =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334376 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334377 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334381 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334382 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35187 (p : Pattern) (selected : d334387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334386 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333611 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333612 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333613 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334387 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35188 (p : Pattern) (selected : d334394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334383 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35185 q selected
    | true =>
      simp only [d334383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35186 q selected
  have h2 (q : Pattern) (selected : d334384 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334385 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334388 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35186 q selected
    | true =>
      simp only [d334388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35187 q selected
  have h5 (q : Pattern) (selected : d334389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334390 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334391 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334392 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334393 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334394 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35189 (p : Pattern) (selected : d334398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334388 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35186 q selected
    | true =>
      simp only [d334388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35187 q selected
  have h2 (q : Pattern) (selected : d334389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334390 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334392 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334397 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334398 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35190 (p : Pattern) (selected : d334404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35188 q selected
    | true =>
      simp only [d334395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35189 q selected
    | true =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35191 (p : Pattern) (selected : d334408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35189 q selected
    | true =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35192 (p : Pattern) (selected : d334429 p = 1) : d338379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334313 q = 1) : d334313 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334322 q = 1) : d334322 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334353 q = 1) : d334353 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d334409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35190 q selected
    | true =>
      simp only [d334409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35191 q selected
  have h5 (q : Pattern) (selected : d334410 q = 1) : d338375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334410, d338375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334410, d338375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334425 q = 1) : d334425 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d334426 q = 1) : d338376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334426, d338376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334426, d338376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334427 q = 1) : d338377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334427, d338377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334427, d338377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334428 q = 1) : d338378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334428, d338378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334428, d338378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334429 q = 1) : d338379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334429, d338379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334429, d338379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35193 (p : Pattern) (selected : d334443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334395 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35188 q selected
    | true =>
      simp only [d334395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334396 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35189 q selected
    | true =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334443 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35194 (p : Pattern) (selected : d334444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35189 q selected
    | true =>
      simp only [d334399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35195 (p : Pattern) (selected : d334453 p = 1) : d338384 p = 1 := by
  have h0 (q : Pattern) (selected : d334313 q = 1) : d334313 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334322 q = 1) : d334322 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334353 q = 1) : d334353 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35190 q selected
    | true =>
      simp only [d334409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35191 q selected
  have h4 (q : Pattern) (selected : d334410 q = 1) : d338375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334410, d338375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334410, d338375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334425 q = 1) : d334425 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d334426 q = 1) : d338376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334426, d338376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334426, d338376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334427 q = 1) : d338377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334427, d338377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334427, d338377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334428 q = 1) : d338378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334428, d338378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334428, d338378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334435 q = 1) : d334435 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d334440 q = 1) : d334440 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d334442 q = 1) : d334442 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d334445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35193 q selected
    | true =>
      simp only [d334445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35194 q selected
  have h13 (q : Pattern) (selected : d334446 q = 1) : d338380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334446, d338380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334446, d338380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334449 q = 1) : d334449 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d334450 q = 1) : d338381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334450, d338381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334450, d338381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334451 q = 1) : d338382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334451, d338382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334451, d338382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334452 q = 1) : d338383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334452, d338383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334452, d338383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334453 q = 1) : d338384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334453, d338384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334453, d338384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro35196 (p : Pattern) (selected : d334473 p = 1) : d338391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334442 q = 1) : d334442 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35193 q selected
    | true =>
      simp only [d334445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35194 q selected
  have h3 (q : Pattern) (selected : d334446 q = 1) : d338380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334446, d338380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334446, d338380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334449 q = 1) : d334449 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334450 q = 1) : d338381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334450, d338381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334450, d338381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334471 q = 1) : d338389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334471, d338389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334471, d338389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334472 q = 1) : d338390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334472, d338390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334472, d338390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334473 q = 1) : d338391 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334473, d338391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334473, d338391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35197 (p : Pattern) (selected : d334553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334539 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35182 q selected
  have h2 (q : Pattern) (selected : d334361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35182 q selected
    | true =>
      simp only [d334361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334540 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334541 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334542 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35183 q selected
  have h8 (q : Pattern) (selected : d334366 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35183 q selected
    | true =>
      simp only [d334366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334545 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334546 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334547 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334548 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
  have h15 (q : Pattern) (selected : d334374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
    | true =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334549 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334550 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334551 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334552 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334553 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35198 (p : Pattern) (selected : d334556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334176 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
  have h2 (q : Pattern) (selected : d334026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35160 q selected
    | true =>
      simp only [d334026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334177 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334178 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334179 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
  have h8 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334554 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334548 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
  have h15 (q : Pattern) (selected : d334374 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35184 q selected
    | true =>
      simp only [d334374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334549 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334375 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334550 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334551 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334555 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334556 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35199 (p : Pattern) (selected : d334561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d333875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
  have h2 (q : Pattern) (selected : d333782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35146 q selected
    | true =>
      simp only [d333782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334560 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333684 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
  have h9 (q : Pattern) (selected : d333609 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35132 q selected
    | true =>
      simp only [d333609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333686 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333687 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333688 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334561 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35200 (p : Pattern) (selected : d334568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334557 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35197 q selected
    | true =>
      simp only [d334557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35198 q selected
  have h2 (q : Pattern) (selected : d334558 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334559 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35198 q selected
    | true =>
      simp only [d334562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35199 q selected
  have h5 (q : Pattern) (selected : d334563 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334564 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334565 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334566 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334567 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334568 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35201 (p : Pattern) (selected : d334572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334562 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35198 q selected
    | true =>
      simp only [d334562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35199 q selected
  have h2 (q : Pattern) (selected : d334563 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334564 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334566 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334571 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334572 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35202 (p : Pattern) (selected : d334578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334569 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35200 q selected
    | true =>
      simp only [d334569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334570 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334573 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35201 q selected
    | true =>
      simp only [d334573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334574 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334575 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334576 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334577 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334578 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35203 (p : Pattern) (selected : d334582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334573 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35201 q selected
    | true =>
      simp only [d334573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334574 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35204 (p : Pattern) (selected : d334603 p = 1) : d338401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334538 q = 1) : d334538 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35202 q selected
    | true =>
      simp only [d334583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35203 q selected
  have h3 (q : Pattern) (selected : d334584 q = 1) : d338397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334584, d338397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334584, d338397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334599 q = 1) : d334599 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334600 q = 1) : d338398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334600, d338398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334600, d338398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334601 q = 1) : d338399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334601, d338399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334601, d338399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334602 q = 1) : d338400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334602, d338400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334602, d338400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334603 q = 1) : d338401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334603, d338401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334603, d338401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35205 (p : Pattern) (selected : d334620 p = 1) : d338407 p = 1 := by
  have h0 (q : Pattern) (selected : d334305 q = 1) : d334305 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334454 q = 1) : d338385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334454, d338385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35192 q selected
    | true =>
      simp only [d334454, d338385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35195 q selected
  have h2 (q : Pattern) (selected : d334467 q = 1) : d334467 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334468 q = 1) : d338386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334468, d338386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334468, d338386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334469 q = 1) : d338387 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334469, d338387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334469, d338387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334470 q = 1) : d338388 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334470, d338388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334470, d338388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334474 q = 1) : d338392 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334474, d338392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334474, d338392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35196 q selected
  have h8 (q : Pattern) (selected : d334476 q = 1) : d334476 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d334477 q = 1) : d338393 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334477, d338393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334477, d338393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334478 q = 1) : d338394 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334478, d338394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334478, d338394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d334479 q = 1) : d338395 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334479, d338395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334479, d338395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d334480 q = 1) : d338396 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334480, d338396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334480, d338396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334604 q = 1) : d338402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334604, d338402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334604, d338402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35204 q selected
  have h14 (q : Pattern) (selected : d334615 q = 1) : d334615 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d334616 q = 1) : d338403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334616, d338403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334616, d338403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334617 q = 1) : d338404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334617, d338404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334617, d338404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d334618 q = 1) : d338405 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334618, d338405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334618, d338405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d334619 q = 1) : d338406 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334619, d338406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334619, d338406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d334620 q = 1) : d338407 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d334620, d338407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334620, d338407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro35206 (p : Pattern) (selected : d334626 p = 1) : d338413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334621 q = 1) : d338408 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d334621, d338408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334621, d338408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35205 q selected
  have h2 (q : Pattern) (selected : d334622 q = 1) : d338409 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d334622, d338409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334622, d338409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334623 q = 1) : d338410 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d334623, d338410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334623, d338410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334624 q = 1) : d338411 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d334624, d338411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334624, d338411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334625 q = 1) : d338412 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d334625, d338412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334625, d338412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334626 q = 1) : d338413 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d334626, d338413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334626, d338413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35207 (p : Pattern) (selected : d334762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334759 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334760 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334761 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334762 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35208 (p : Pattern) (selected : d334769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334354 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23840 q selected
    | true =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334759 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334767 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334768 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334769 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro35209 (p : Pattern) (selected : d334780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334759 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334775 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334776 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334777 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
    | true =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h5 (q : Pattern) (selected : d334778 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334779 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334780 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35210 (p : Pattern) (selected : d334786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334763 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35207 q selected
    | true =>
      simp only [d334763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334764 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334765 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334766 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334770 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35208 q selected
    | true =>
      simp only [d334770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334772 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334773 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334774 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
    | true =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334785 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334786 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35211 (p : Pattern) (selected : d334790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334354 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23840 q selected
    | true =>
      simp only [d334354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334759 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334767 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334768 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334787 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d334787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334788 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334789 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334790 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35212 (p : Pattern) (selected : d334795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334759 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d334759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334787 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d334787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334788 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334789 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334777 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
    | true =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h6 (q : Pattern) (selected : d334778 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334779 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334795 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35213 (p : Pattern) (selected : d334802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35211 q selected
    | true =>
      simp only [d334791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334796 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
    | true =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334797 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334798 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334799 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334800 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
    | true =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334783 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334784 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334801 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334802 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35214 (p : Pattern) (selected : d334807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d334777 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
    | true =>
      simp only [d334777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334778 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334779 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d334807 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro35215 (p : Pattern) (selected : d334813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334796 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
    | true =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334797 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334798 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334799 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334806 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334808 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35214 q selected
    | true =>
      simp only [d334808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334809 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334810 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334811 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334812 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334813 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35216 (p : Pattern) (selected : d334820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334803 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35210 q selected
    | true =>
      simp only [d334803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35213 q selected
  have h2 (q : Pattern) (selected : d334804 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334805 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35213 q selected
    | true =>
      simp only [d334814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35215 q selected
  have h5 (q : Pattern) (selected : d334815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334818 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334819 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334820 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35217 (p : Pattern) (selected : d334824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35213 q selected
    | true =>
      simp only [d334814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35215 q selected
  have h2 (q : Pattern) (selected : d334815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334818 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334823 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35218 (p : Pattern) (selected : d334830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334821 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35216 q selected
    | true =>
      simp only [d334821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334822 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35217 q selected
    | true =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35219 (p : Pattern) (selected : d334834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35217 q selected
    | true =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334831 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334832 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334833 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334834 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35220 (p : Pattern) (selected : d334870 p = 1) : d338421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334732 q = 1) : d334732 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334741 q = 1) : d334741 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334758 q = 1) : d334758 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d334835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35218 q selected
    | true =>
      simp only [d334835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35219 q selected
  have h5 (q : Pattern) (selected : d334836 q = 1) : d338417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334836, d338417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334836, d338417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334866 q = 1) : d334866 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d334867 q = 1) : d338418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334867, d338418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334867, d338418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334868 q = 1) : d338419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334868, d338419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334868, d338419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334869 q = 1) : d338420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334869, d338420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334869, d338420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334870 q = 1) : d338421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334870, d338421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334870, d338421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35221 (p : Pattern) (selected : d334884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334821 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35216 q selected
    | true =>
      simp only [d334821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334822 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35217 q selected
    | true =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334884 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35222 (p : Pattern) (selected : d334885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35217 q selected
    | true =>
      simp only [d334825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334831 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334832 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334833 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334885 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35223 (p : Pattern) (selected : d334894 p = 1) : d338426 p = 1 := by
  have h0 (q : Pattern) (selected : d334732 q = 1) : d334732 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334741 q = 1) : d334741 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334758 q = 1) : d334758 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35218 q selected
    | true =>
      simp only [d334835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35219 q selected
  have h4 (q : Pattern) (selected : d334836 q = 1) : d338417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334836, d338417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334836, d338417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334866 q = 1) : d334866 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d334867 q = 1) : d338418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334867, d338418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334867, d338418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334868 q = 1) : d338419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334868, d338419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334868, d338419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334869 q = 1) : d338420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334869, d338420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334869, d338420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334876 q = 1) : d334876 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d334881 q = 1) : d334881 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d334883 q = 1) : d334883 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d334886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35221 q selected
    | true =>
      simp only [d334886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35222 q selected
  have h13 (q : Pattern) (selected : d334887 q = 1) : d338422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334887, d338422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334887, d338422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334890 q = 1) : d334890 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d334891 q = 1) : d338423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334891, d338423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334891, d338423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334892 q = 1) : d338424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334892, d338424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334892, d338424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334893 q = 1) : d338425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334893, d338425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334893, d338425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334894 q = 1) : d338426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334894, d338426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334894, d338426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro35224 (p : Pattern) (selected : d334914 p = 1) : d338433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334883 q = 1) : d334883 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d334886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35221 q selected
    | true =>
      simp only [d334886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35222 q selected
  have h3 (q : Pattern) (selected : d334887 q = 1) : d338422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334887, d338422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334887, d338422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334890 q = 1) : d334890 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334891 q = 1) : d338423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334891, d338423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334891, d338423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334912 q = 1) : d338431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334912, d338431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334912, d338431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334913 q = 1) : d338432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334913, d338432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334913, d338432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334914 q = 1) : d338433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334914, d338433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334914, d338433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35225 (p : Pattern) (selected : d335006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334992 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35207 q selected
  have h2 (q : Pattern) (selected : d334763 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35207 q selected
    | true =>
      simp only [d334763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334993 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334764 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334994 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334995 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35208 q selected
  have h8 (q : Pattern) (selected : d334770 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35208 q selected
    | true =>
      simp only [d334770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335000 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335001 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
  have h15 (q : Pattern) (selected : d334781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
    | true =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335002 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335003 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335004 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d335006 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35226 (p : Pattern) (selected : d335017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35211 q selected
  have h2 (q : Pattern) (selected : d334791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35211 q selected
    | true =>
      simp only [d334791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
  have h8 (q : Pattern) (selected : d334796 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
    | true =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334797 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d335014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d335015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335001 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
  have h15 (q : Pattern) (selected : d334781 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35209 q selected
    | true =>
      simp only [d334781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d335002 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d335002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334782 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d335003 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d335004 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d335004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d335016 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d335016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d335017 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro35227 (p : Pattern) (selected : d335027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
  have h2 (q : Pattern) (selected : d334796 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35212 q selected
    | true =>
      simp only [d334796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334797 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335021 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335022 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35214 q selected
  have h9 (q : Pattern) (selected : d334808 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35214 q selected
    | true =>
      simp only [d334808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335023 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334809 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335024 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335025 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335026 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335027 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35228 (p : Pattern) (selected : d335034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335018 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35225 q selected
    | true =>
      simp only [d335018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35226 q selected
  have h2 (q : Pattern) (selected : d335019 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335020 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335028 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35226 q selected
    | true =>
      simp only [d335028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35227 q selected
  have h5 (q : Pattern) (selected : d335029 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335030 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335031 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335032 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335033 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335034 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35229 (p : Pattern) (selected : d335038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335028 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35226 q selected
    | true =>
      simp only [d335028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35227 q selected
  have h2 (q : Pattern) (selected : d335029 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335030 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335032 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335037 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335038 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35230 (p : Pattern) (selected : d335044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335035 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35228 q selected
    | true =>
      simp only [d335035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335036 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35229 q selected
    | true =>
      simp only [d335039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335041 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35231 (p : Pattern) (selected : d335048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35229 q selected
    | true =>
      simp only [d335039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35232 (p : Pattern) (selected : d335080 p = 1) : d338443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334991 q = 1) : d334991 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d335049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35230 q selected
    | true =>
      simp only [d335049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35231 q selected
  have h3 (q : Pattern) (selected : d335050 q = 1) : d338439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335050, d338439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335050, d338439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335076 q = 1) : d335076 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d335077 q = 1) : d338440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335077, d338440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335077, d338440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335078 q = 1) : d338441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335078, d338441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335078, d338441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335079 q = 1) : d338442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335079, d338442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335079, d338442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335080 q = 1) : d338443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335080, d338443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335080, d338443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35233 (p : Pattern) (selected : d335097 p = 1) : d338449 p = 1 := by
  have h0 (q : Pattern) (selected : d334724 q = 1) : d334724 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d334895 q = 1) : d338427 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334895, d338427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35220 q selected
    | true =>
      simp only [d334895, d338427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35223 q selected
  have h2 (q : Pattern) (selected : d334908 q = 1) : d334908 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d334909 q = 1) : d338428 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334909, d338428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334909, d338428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d334910 q = 1) : d338429 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334910, d338429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334910, d338429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334911 q = 1) : d338430 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334911, d338430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334911, d338430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334915 q = 1) : d338434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334915, d338434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334915, d338434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35224 q selected
  have h8 (q : Pattern) (selected : d334917 q = 1) : d334917 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d334918 q = 1) : d338435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334918, d338435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334918, d338435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334919 q = 1) : d338436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334919, d338436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334919, d338436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d334920 q = 1) : d338437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334920, d338437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334920, d338437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d334921 q = 1) : d338438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334921, d338438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334921, d338438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335081 q = 1) : d338444 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d335081, d338444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335081, d338444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35232 q selected
  have h14 (q : Pattern) (selected : d335092 q = 1) : d335092 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d335093 q = 1) : d338445 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d335093, d338445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335093, d338445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335094 q = 1) : d338446 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d335094, d338446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d335094, d338446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d335095 q = 1) : d338447 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d335095, d338447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d335095, d338447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d335096 q = 1) : d338448 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d335096, d338448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d335096, d338448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d335097 q = 1) : d338449 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d335097, d338449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335097, d338449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro35234 (p : Pattern) (selected : d335103 p = 1) : d338455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335098 q = 1) : d338450 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d335098, d338450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335098, d338450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35233 q selected
  have h2 (q : Pattern) (selected : d335099 q = 1) : d338451 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d335099, d338451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335099, d338451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335100 q = 1) : d338452 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d335100, d338452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335100, d338452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335101 q = 1) : d338453 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d335101, d338453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335101, d338453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335102 q = 1) : d338454 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d335102, d338454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335102, d338454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335103 q = 1) : d338455 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d335103, d338455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335103, d338455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35235 (p : Pattern) (selected : d335222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
    | true =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h2 (q : Pattern) (selected : d335220 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335221 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335222 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35236 (p : Pattern) (selected : d335228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35235 q selected
    | true =>
      simp only [d335223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335225 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335226 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335227 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335228 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35237 (p : Pattern) (selected : d335232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335229 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d335229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335230 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335231 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335232 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro35238 (p : Pattern) (selected : d335237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335229 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d335229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335230 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335231 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
    | true =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h5 (q : Pattern) (selected : d335220 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335221 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335237 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro35239 (p : Pattern) (selected : d335244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335233 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35237 q selected
    | true =>
      simp only [d335233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335234 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335235 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335236 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335238 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35238 q selected
    | true =>
      simp only [d335238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335239 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335240 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335241 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335242 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335223 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35235 q selected
    | true =>
      simp only [d335223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335224 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d335225 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d335226 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d335226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d335243 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d335244 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro35240 (p : Pattern) (selected : d335249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d335219 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
    | true =>
      simp only [d335219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d335220 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335221 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d335249 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d335249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro35241 (p : Pattern) (selected : d335255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335238 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35238 q selected
    | true =>
      simp only [d335238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335239 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d335240 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335241 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335248 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335250 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d335250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35240 q selected
    | true =>
      simp only [d335250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335251 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d335251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335252 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d335252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335253 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d335253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d335254 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d335254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d335255 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d335255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro35242 (p : Pattern) (selected : d335262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335245 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35236 q selected
    | true =>
      simp only [d335245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35239 q selected
  have h2 (q : Pattern) (selected : d335246 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335247 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335256 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35239 q selected
    | true =>
      simp only [d335256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35241 q selected
  have h5 (q : Pattern) (selected : d335257 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335258 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335259 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335260 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d335261 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335262 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro35243 (p : Pattern) (selected : d335266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335256 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d335256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35239 q selected
    | true =>
      simp only [d335256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35241 q selected
  have h2 (q : Pattern) (selected : d335257 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d335257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335258 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d335258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d335260 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d335260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335265 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d335265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335266 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d335266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35244 (p : Pattern) (selected : d335272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35242 q selected
    | true =>
      simp only [d335263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35243 q selected
    | true =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335269 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335270 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335271 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335272 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro35245 (p : Pattern) (selected : d335276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35243 q selected
    | true =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335273 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro35246 (p : Pattern) (selected : d335312 p = 1) : d338464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335192 q = 1) : d335192 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d335201 q = 1) : d335201 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d335218 q = 1) : d335218 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d335277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35244 q selected
    | true =>
      simp only [d335277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35245 q selected
  have h5 (q : Pattern) (selected : d335278 q = 1) : d338460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335278, d338460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335278, d338460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335308 q = 1) : d335308 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d335309 q = 1) : d338461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335309, d338461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335309, d338461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335310 q = 1) : d338462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335310, d338462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335310, d338462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335311 q = 1) : d338463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335311, d338463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335311, d338463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d335312 q = 1) : d338464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335312, d338464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335312, d338464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro35247 (p : Pattern) (selected : d335326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35242 q selected
    | true =>
      simp only [d335263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35243 q selected
    | true =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335269 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d335270 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335271 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d335326 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d335326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro35248 (p : Pattern) (selected : d335327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35243 q selected
    | true =>
      simp only [d335267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d335268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d335273 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d335273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d335274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d335274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d335274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d335275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d335327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d335327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d335327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro35249 (p : Pattern) (selected : d335336 p = 1) : d338469 p = 1 := by
  have h0 (q : Pattern) (selected : d335192 q = 1) : d335192 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d335201 q = 1) : d335201 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d335218 q = 1) : d335218 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d335277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35244 q selected
    | true =>
      simp only [d335277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35245 q selected
  have h4 (q : Pattern) (selected : d335278 q = 1) : d338460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335278, d338460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d335278, d338460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d335308 q = 1) : d335308 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d335309 q = 1) : d338461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335309, d338461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d335309, d338461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d335310 q = 1) : d338462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335310, d338462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d335310, d338462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d335311 q = 1) : d338463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335311, d338463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d335311, d338463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d335318 q = 1) : d335318 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d335323 q = 1) : d335323 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d335325 q = 1) : d335325 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d335328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d335328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35247 q selected
    | true =>
      simp only [d335328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35248 q selected
  have h13 (q : Pattern) (selected : d335329 q = 1) : d338465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d335329, d338465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d335329, d338465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d335332 q = 1) : d335332 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d335333 q = 1) : d338466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d335333, d338466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d335333, d338466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d335334 q = 1) : d338467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d335334, d338467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d335334, d338467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d335335 q = 1) : d338468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d335335, d338468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d335335, d338468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d335336 q = 1) : d338469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d335336, d338469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d335336, d338469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
end NetHack.Soko22Hazard87
