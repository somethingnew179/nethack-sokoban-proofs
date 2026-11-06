import NetHack.Soko22Hazard87.AndIntroBlocks0210
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro52750 (p : Pattern) (ha : d113664 p = 1) (hb : d162831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d162729 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52724 q ha hb
    | true =>
      simp only [d113554, d162729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d162730 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d162730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d162806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d162806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d162807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d162807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d162808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d162808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113664 q = 1) (hb : d162831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113664, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113664, d162831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52751 (p : Pattern) (ha : d113670 p = 1) (hb : d162837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d162766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52732 q ha hb
    | true =>
      simp only [d113591, d162766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52733 q ha hb
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d162767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d162767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d162768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d162768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d162769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d162769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d162776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52734 q ha hb
    | true =>
      simp only [d113601, d162776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52735 q ha hb
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d162777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d162777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d162778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d162778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d162804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52740 q ha hb
    | true =>
      simp only [d113637, d162804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52741 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d162805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d162805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d162810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52742 q ha hb
    | true =>
      simp only [d113643, d162810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d162811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d162811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d162812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d162812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d162813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d162813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d162814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d162814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113651 q = 1) (hb : d162818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113651, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52744 q ha hb
    | true =>
      simp only [d113651, d162818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52745 q ha hb
  have h17 (q : Pattern) (ha : d113652 q = 1) (hb : d162819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113652, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113652, d162819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113653 q = 1) (hb : d162820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113653, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113653, d162820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113654 q = 1) (hb : d162821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113654, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113654, d162821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113657 q = 1) (hb : d162824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113657, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52746 q ha hb
    | true =>
      simp only [d113657, d162824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52747 q ha hb
  have h21 (q : Pattern) (ha : d113658 q = 1) (hb : d162825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113658, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113658, d162825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113659 q = 1) (hb : d162826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113659, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113659, d162826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113662 q = 1) (hb : d162829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52748 q ha hb
    | true =>
      simp only [d113662, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52749 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113663 q = 1) (hb : d162830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113663, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113665 q = 1) (hb : d162832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52750 q ha hb
    | true =>
      simp only [d113665, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113666 q = 1) (hb : d162833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113666, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113667 q = 1) (hb : d162834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113667, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113668 q = 1) (hb : d162835 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113668, d162835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113669 q = 1) (hb : d162836 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113669, d162836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113670 q = 1) (hb : d162837 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113670, d162837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52752 (p : Pattern) (ha : d113682 p = 1) (hb : d162849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113672 q = 1) (hb : d162839 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113672, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52741 q ha hb
    | true =>
      simp only [d113672, d162839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
  have h2 (q : Pattern) (ha : d113673 q = 1) (hb : d162840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113673, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113673, d162840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113674 q = 1) (hb : d162841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113674, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113674, d162841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113675 q = 1) (hb : d162842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113675, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113675, d162842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113676 q = 1) (hb : d162843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113676, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113676, d162843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113677 q = 1) (hb : d162844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113677, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
    | true =>
      simp only [d113677, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113678 q = 1) (hb : d162845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113678, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113678, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113679 q = 1) (hb : d162846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113679, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113679, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113680 q = 1) (hb : d162847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113680, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113680, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113681 q = 1) (hb : d162848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113681, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113681, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113682 q = 1) (hb : d162849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113682, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113682, d162849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52753 (p : Pattern) (ha : d113688 p = 1) (hb : d162855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113677 q = 1) (hb : d162844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113677, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
    | true =>
      simp only [d113677, d162844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113678 q = 1) (hb : d162845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113678, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113678, d162845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113679 q = 1) (hb : d162846 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113679, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113679, d162846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113680 q = 1) (hb : d162847 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113680, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113680, d162847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113681 q = 1) (hb : d162848 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113681, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113681, d162848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113683 q = 1) (hb : d162850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113683, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52730 q ha hb
    | true =>
      simp only [d113683, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113684 q = 1) (hb : d162851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113684, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113684, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113685 q = 1) (hb : d162852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113685, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113685, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113686 q = 1) (hb : d162853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113686, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113686, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113687 q = 1) (hb : d162854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113687, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113687, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113688 q = 1) (hb : d162855 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113688, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113688, d162855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52754 (p : Pattern) (ha : d113695 p = 1) (hb : d162862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113662 q = 1) (hb : d162829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52748 q ha hb
    | true =>
      simp only [d113662, d162829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52749 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d162830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113663, d162830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113665 q = 1) (hb : d162832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52750 q ha hb
    | true =>
      simp only [d113665, d162832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113666 q = 1) (hb : d162833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113666, d162833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113667 q = 1) (hb : d162834 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d162834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113693 q = 1) (hb : d162860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d162860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113694 q = 1) (hb : d162861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d162861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113695 q = 1) (hb : d162862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d162862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52755 (p : Pattern) (ha : d113697 p = 1) (hb : d162864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113683 q = 1) (hb : d162850 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113683, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52730 q ha hb
    | true =>
      simp only [d113683, d162850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113684 q = 1) (hb : d162851 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113684, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113684, d162851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113685 q = 1) (hb : d162852 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113685, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113685, d162852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113686 q = 1) (hb : d162853 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113686, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113686, d162853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113687 q = 1) (hb : d162854 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113687, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113687, d162854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113697 q = 1) (hb : d162864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113697, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113697, d162864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52756 (p : Pattern) (ha : d13495 p = 1) (hb : d113717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
  have h2 (q : Pattern) (ha : d10099 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13487 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13487, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10101 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13488 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13488, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13489 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13489, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13494 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13494, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13495 q = 1) (hb : d113717 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, d113717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13495, d113717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro52757 (p : Pattern) (ha : d76224 p = 1) (hb : d162881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22529 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
  have h8 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22530 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22531 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22532 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53198 q = 1) (hb : d162880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53198, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53198, d162880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76224 q = 1) (hb : d162881 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d76224, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76224, d162881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52758 (p : Pattern) (ha : d113703 p = 1) (hb : d162870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17006 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17007 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17008 q = 1) (hb : d53187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17008, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113703 q = 1) (hb : d162870 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113703, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113703, d162870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52759 (p : Pattern) (ha : d113704 p = 1) (hb : d162872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53192 q = 1) (hb : d162871 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53192, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53192, d162871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d113704 q = 1) (hb : d162872 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113704, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113704, d162872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52760 (p : Pattern) (ha : d113727 p = 1) (hb : d162890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113705 q = 1) (hb : d162873 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113705, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52758 q ha hb
    | true =>
      simp only [d113705, d162873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52759 q ha hb
  have h2 (q : Pattern) (ha : d113706 q = 1) (hb : d162874 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113706, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113706, d162874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113707 q = 1) (hb : d162875 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113707, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113707, d162875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113718 q = 1) (hb : d162876 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113718, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52759 q ha hb
    | true =>
      simp only [d113718, d162876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52756 q hb ha
  have h5 (q : Pattern) (ha : d113719 q = 1) (hb : d162877 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113719, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113719, d162877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113720 q = 1) (hb : d162878 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113720, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113720, d162878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113721 q = 1) (hb : d162879 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113721, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113721, d162879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113722 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52759 q ha hb
    | true =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
  have h9 (q : Pattern) (ha : d113723 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113724 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76231 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
    | true =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q hb ha
  have h12 (q : Pattern) (ha : d76232 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76233 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113725 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113726 q = 1) (hb : d162889 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113726, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113726, d162889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113727 q = 1) (hb : d162890 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113727, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113727, d162890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52761 (p : Pattern) (ha : d113731 p = 1) (hb : d162895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113722 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52759 q ha hb
    | true =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
  have h2 (q : Pattern) (ha : d113723 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113724 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76231 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
    | true =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q hb ha
  have h5 (q : Pattern) (ha : d76232 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76233 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113725 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76234 q = 1) (hb : d162893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76234, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76234, d162893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113730 q = 1) (hb : d162894 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113730, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113730, d162894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113731 q = 1) (hb : d162895 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113731, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113731, d162895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52762 (p : Pattern) (ha : d113737 p = 1) (hb : d162901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113728 q = 1) (hb : d162891 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113728, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52760 q ha hb
    | true =>
      simp only [d113728, d162891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113729 q = 1) (hb : d162892 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113729, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113729, d162892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113732 q = 1) (hb : d162896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52761 q ha hb
    | true =>
      simp only [d113732, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113733 q = 1) (hb : d162897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113734 q = 1) (hb : d162898 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113734, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113734, d162898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113735 q = 1) (hb : d162899 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113735, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113735, d162899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113736 q = 1) (hb : d162900 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113736, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113736, d162900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113737 q = 1) (hb : d162901 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113737, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113737, d162901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52763 (p : Pattern) (ha : d113744 p = 1) (hb : d162907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113739 q = 1) (hb : d162902 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113739, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
    | true =>
      simp only [d113739, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q hb ha
  have h2 (q : Pattern) (ha : d113740 q = 1) (hb : d162903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113740, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113740, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113741 q = 1) (hb : d162904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113741, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113741, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113742 q = 1) (hb : d162905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113742, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113742, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113743 q = 1) (hb : d162906 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113743, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113743, d162906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113744 q = 1) (hb : d162907 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113744, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113744, d162907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52764 (p : Pattern) (ha : d113750 p = 1) (hb : d162913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113732 q = 1) (hb : d162896 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52761 q ha hb
    | true =>
      simp only [d113732, d162896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113733 q = 1) (hb : d162897 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d162897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52763 q ha hb
    | true =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113747 q = 1) (hb : d162910 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113747, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113747, d162910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113748 q = 1) (hb : d162911 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113748, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113748, d162911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113749 q = 1) (hb : d162912 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113749, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113749, d162912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113750 q = 1) (hb : d162913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113750, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113750, d162913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52765 (p : Pattern) (ha : d113753 p = 1) (hb : d162917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113722 q = 1) (hb : d162882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52759 q ha hb
    | true =>
      simp only [d113722, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
  have h2 (q : Pattern) (ha : d113723 q = 1) (hb : d162883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113724 q = 1) (hb : d162884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76231 q = 1) (hb : d162885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
    | true =>
      simp only [d76231, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q hb ha
  have h5 (q : Pattern) (ha : d76232 q = 1) (hb : d162886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76233 q = 1) (hb : d162887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113725 q = 1) (hb : d162888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113725, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113739 q = 1) (hb : d162902 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113739, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52757 q ha hb
    | true =>
      simp only [d113739, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q hb ha
  have h9 (q : Pattern) (ha : d113740 q = 1) (hb : d162903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113740, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113740, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113741 q = 1) (hb : d162904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113741, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113741, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113742 q = 1) (hb : d162905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113742, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113742, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113752 q = 1) (hb : d162916 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113752, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113752, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113753 q = 1) (hb : d162917 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113753, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113753, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52766 (p : Pattern) (ha : d113769 p = 1) (hb : d162923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d162918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52765 q ha hb
    | true =>
      simp only [d113754, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d162919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113766 q = 1) (hb : d162920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113766, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113766, d162920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113767 q = 1) (hb : d162921 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113767, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113767, d162921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113768 q = 1) (hb : d162922 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113768, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113768, d162922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113769 q = 1) (hb : d162923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113769, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113769, d162923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52767 (p : Pattern) (ha : d113775 p = 1) (hb : d162929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113751 q = 1) (hb : d162914 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113751, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52762 q ha hb
    | true =>
      simp only [d113751, d162914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52764 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d162915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113765, d162915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113770 q = 1) (hb : d162924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113770, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52766 q ha hb
    | true =>
      simp only [d113770, d162924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113771 q = 1) (hb : d162925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113771, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113771, d162925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113772 q = 1) (hb : d162926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d162926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113773 q = 1) (hb : d162927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d162927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113774 q = 1) (hb : d162928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d162928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113775 q = 1) (hb : d162929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d162929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52768 (p : Pattern) (ha : d113763 p = 1) (hb : d162934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113745 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52763 q ha hb
    | true =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113746 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113760 q = 1) (hb : d162931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113760, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113760, d162931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113761 q = 1) (hb : d162932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113761, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113761, d162932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113762 q = 1) (hb : d162933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113762, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113762, d162933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113763 q = 1) (hb : d162934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113763, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113763, d162934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52769 (p : Pattern) (ha : d113782 p = 1) (hb : d162940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113777 q = 1) (hb : d162935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113777, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52768 q ha hb
    | true =>
      simp only [d113777, d162935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113778 q = 1) (hb : d162936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113778, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113778, d162936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113779 q = 1) (hb : d162937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113779, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113779, d162937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113780 q = 1) (hb : d162938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113780, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113780, d162938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113781 q = 1) (hb : d162939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113781, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113781, d162939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113782 q = 1) (hb : d162940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113782, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113782, d162940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52770 (p : Pattern) (ha : d113788 p = 1) (hb : d162946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113574 q = 1) (hb : d162749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113574, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113574, d162749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52728 q ha hb
  have h2 (q : Pattern) (ha : d113575 q = 1) (hb : d162750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113575, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113575, d162750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113584 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113584, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52728 q ha hb
    | true =>
      simp only [d113584, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52731 q ha hb
  have h4 (q : Pattern) (ha : d113585 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113585, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113585, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113586 q = 1) (hb : d162761 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113586, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113586, d162761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113671 q = 1) (hb : d162838 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52743 q ha hb
    | true =>
      simp only [d113671, d162838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52751 q ha hb
  have h7 (q : Pattern) (ha : d113689 q = 1) (hb : d162856 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113689, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52752 q ha hb
    | true =>
      simp only [d113689, d162856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52753 q ha hb
  have h8 (q : Pattern) (ha : d113690 q = 1) (hb : d162857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113690, d162857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113691 q = 1) (hb : d162858 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113691, d162858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113692 q = 1) (hb : d162859 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113692, d162859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113696 q = 1) (hb : d162863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113696, d162863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52754 q ha hb
  have h12 (q : Pattern) (ha : d113698 q = 1) (hb : d162865 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113698, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113698, d162865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52755 q ha hb
  have h13 (q : Pattern) (ha : d113699 q = 1) (hb : d162866 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113699, d162866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113700 q = 1) (hb : d162867 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113700, d162867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113701 q = 1) (hb : d162868 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113701, d162868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113702 q = 1) (hb : d162869 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113702, d162869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113776 q = 1) (hb : d162930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113776, d162930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52767 q ha hb
  have h18 (q : Pattern) (ha : d113783 q = 1) (hb : d162941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113783, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113783, d162941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52769 q ha hb
  have h19 (q : Pattern) (ha : d113784 q = 1) (hb : d162942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113784, d162942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113785 q = 1) (hb : d162943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113785, d162943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113786 q = 1) (hb : d162944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113786, d162944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113787 q = 1) (hb : d162945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113787, d162945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113788 q = 1) (hb : d162946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113788, d162946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52771 (p : Pattern) (ha : d113794 p = 1) (hb : d162952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d162947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d162947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52770 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d162948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d162948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d162949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d162949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d162950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d162950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d162951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d162951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d162952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d162952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52772 (p : Pattern) (ha : d69321 p = 1) (hb : d162959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53348 q = 1) (hb : d162958 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53348, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53348, d162958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69321 q = 1) (hb : d162959 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d69321, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69321, d162959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52773 (p : Pattern) (ha : d113799 p = 1) (hb : d162957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17155 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17155, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113799 q = 1) (hb : d162957 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113799, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113799, d162957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52774 (p : Pattern) (ha : d113810 p = 1) (hb : d162972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113800 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52773 q ha hb
    | true =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
  have h2 (q : Pattern) (ha : d113801 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113802 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69337 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
    | true =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q hb ha
  have h5 (q : Pattern) (ha : d69338 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69339 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113803 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113805 q = 1) (hb : d162967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113805, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
    | true =>
      simp only [d113805, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q hb ha
  have h9 (q : Pattern) (ha : d113806 q = 1) (hb : d162968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113806, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113806, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113807 q = 1) (hb : d162969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113807, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113807, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113808 q = 1) (hb : d162970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113808, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113808, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113809 q = 1) (hb : d162971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113809, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113809, d162971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113810 q = 1) (hb : d162972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113810, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113810, d162972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52775 (p : Pattern) (ha : d113814 p = 1) (hb : d162976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113805 q = 1) (hb : d162967 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113805, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
    | true =>
      simp only [d113805, d162967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18730 q hb ha
  have h2 (q : Pattern) (ha : d113806 q = 1) (hb : d162968 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113806, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113806, d162968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113807 q = 1) (hb : d162969 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113807, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113807, d162969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113808 q = 1) (hb : d162970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113808, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113808, d162970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113813 q = 1) (hb : d162975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113813, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113813, d162975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113814 q = 1) (hb : d162976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113814, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113814, d162976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52776 (p : Pattern) (ha : d113820 p = 1) (hb : d162982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d162981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113820 q = 1) (hb : d162982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113820, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113820, d162982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52777 (p : Pattern) (ha : d113824 p = 1) (hb : d162986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d162985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113824 q = 1) (hb : d162986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113824, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113824, d162986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52778 (p : Pattern) (ha : d113830 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52776 q ha hb
    | true =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113830 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113830, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113830, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52779 (p : Pattern) (ha : d113833 p = 1) (hb : d162995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d162981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d162981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113833 q = 1) (hb : d162995 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113833, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113833, d162995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52780 (p : Pattern) (ha : d113834 p = 1) (hb : d162996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d162985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d162985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113834 q = 1) (hb : d162996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113834, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113834, d162996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52781 (p : Pattern) (ha : d113840 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52776 q ha hb
    | true =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113835 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52779 q ha hb
    | true =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52780 q ha hb
  have h7 (q : Pattern) (ha : d113836 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113836, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113836, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113837 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113837, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113837, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113838 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113838, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113838, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113839 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113839, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113839, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113840 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113840, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113840, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52782 (p : Pattern) (ha : d113845 p = 1) (hb : d163007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d163006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113845 q = 1) (hb : d163007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113845, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113845, d163007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52783 (p : Pattern) (ha : d113847 p = 1) (hb : d163009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d163008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113847 q = 1) (hb : d163009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113847, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113847, d163009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52784 (p : Pattern) (ha : d113854 p = 1) (hb : d163016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d163014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d163015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113854 q = 1) (hb : d163016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113854, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113854, d163016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52785 (p : Pattern) (ha : d113857 p = 1) (hb : d163019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d163017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d163018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113857 q = 1) (hb : d163019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113857, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113857, d163019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52786 (p : Pattern) (ha : d113861 p = 1) (hb : d163023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17227 q = 1) (hb : d53427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17227, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113861 q = 1) (hb : d163023 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113861, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113861, d163023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52787 (p : Pattern) (ha : d113879 p = 1) (hb : d163032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113862 q = 1) (hb : d163024 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113862, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52786 q ha hb
    | true =>
      simp only [d113862, d163024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52773 q ha hb
  have h2 (q : Pattern) (ha : d113863 q = 1) (hb : d163025 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113863, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113863, d163025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113864 q = 1) (hb : d163026 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113864, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113864, d163026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113874 q = 1) (hb : d163027 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113874, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52773 q ha hb
    | true =>
      simp only [d113874, d163027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46285 q hb ha
  have h5 (q : Pattern) (ha : d113875 q = 1) (hb : d163028 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113875, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113875, d163028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113876 q = 1) (hb : d163029 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113876, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113876, d163029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113877 q = 1) (hb : d163030 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113877, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113877, d163030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113800 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52773 q ha hb
    | true =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
  have h9 (q : Pattern) (ha : d113801 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113802 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69337 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
    | true =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q hb ha
  have h12 (q : Pattern) (ha : d69338 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69339 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113803 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113878 q = 1) (hb : d163031 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113878, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113878, d163031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113879 q = 1) (hb : d163032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113879, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113879, d163032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52788 (p : Pattern) (ha : d113883 p = 1) (hb : d163037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113800 q = 1) (hb : d162960 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52773 q ha hb
    | true =>
      simp only [d113800, d162960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
  have h2 (q : Pattern) (ha : d113801 q = 1) (hb : d162961 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d162961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113802 q = 1) (hb : d162962 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d162962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69337 q = 1) (hb : d162963 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52772 q ha hb
    | true =>
      simp only [d69337, d162963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q hb ha
  have h5 (q : Pattern) (ha : d69338 q = 1) (hb : d162964 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d162964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69339 q = 1) (hb : d162965 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d162965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113803 q = 1) (hb : d162966 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113803, d162966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69340 q = 1) (hb : d163035 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69340, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69340, d163035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113882 q = 1) (hb : d163036 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113882, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113882, d163036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113883 q = 1) (hb : d163037 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113883, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113883, d163037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52789 (p : Pattern) (ha : d113889 p = 1) (hb : d163043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d163033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52787 q ha hb
    | true =>
      simp only [d113880, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d163034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52788 q ha hb
    | true =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d163040 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d163041 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d163042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113889 q = 1) (hb : d163043 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113889, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113889, d163043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52790 (p : Pattern) (ha : d113893 p = 1) (hb : d163047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52788 q ha hb
    | true =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d163044 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d163045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d163046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113893 q = 1) (hb : d163047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113893, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113893, d163047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52791 (p : Pattern) (ha : d113899 p = 1) (hb : d163053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d163050 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d163051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d163052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113899 q = 1) (hb : d163053 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113899, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113899, d163053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52792 (p : Pattern) (ha : d113905 p = 1) (hb : d163059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d163010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52782 q ha hb
    | true =>
      simp only [d113848, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52783 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d163011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d163012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d163013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d163020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52784 q ha hb
    | true =>
      simp only [d113858, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52785 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d163021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d163022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d163048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52789 q ha hb
    | true =>
      simp only [d113894, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52790 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d163049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d163054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52791 q ha hb
    | true =>
      simp only [d113900, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d163055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d163056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d163057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d163058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113905 q = 1) (hb : d163059 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d163059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52793 (p : Pattern) (ha : d113906 p = 1) (hb : d163060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d162980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d162980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d163006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d163006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113906 q = 1) (hb : d163060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113906, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113906, d163060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52794 (p : Pattern) (ha : d113907 p = 1) (hb : d163061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d162984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d162984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d163008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d163008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113907 q = 1) (hb : d163061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113907, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113907, d163061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52795 (p : Pattern) (ha : d113912 p = 1) (hb : d163066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d162979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d162979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d163014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d163014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d163015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d163015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113912 q = 1) (hb : d163066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113912, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113912, d163066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52796 (p : Pattern) (ha : d113913 p = 1) (hb : d163067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d162983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d162983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d163017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d163017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d163018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d163018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113913 q = 1) (hb : d163067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113913, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113913, d163067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52797 (p : Pattern) (ha : d113917 p = 1) (hb : d163071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d163033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52787 q ha hb
    | true =>
      simp only [d113880, d163033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d163034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d163034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52788 q ha hb
    | true =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d163040 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d163040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d163041 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d163041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d163042 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d163042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113917 q = 1) (hb : d163071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113917, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113917, d163071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52798 (p : Pattern) (ha : d113918 p = 1) (hb : d163072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d163038 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52788 q ha hb
    | true =>
      simp only [d113884, d163038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d163039 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d163039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d162977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52775 q ha hb
    | true =>
      simp only [d113815, d162977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d162978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d162978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d163044 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d163044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d163045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d163045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d163046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d163046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113918 q = 1) (hb : d163072 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113918, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113918, d163072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52799 (p : Pattern) (ha : d113921 p = 1) (hb : d163075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d162973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52774 q ha hb
    | true =>
      simp only [d113811, d162973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d162974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d162974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d163050 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d163050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d163051 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d163051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d163052 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d163052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113921 q = 1) (hb : d163075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113921, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113921, d163075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52800 (p : Pattern) (ha : d113927 p = 1) (hb : d163081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d163010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52782 q ha hb
    | true =>
      simp only [d113848, d163010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52783 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d163011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d163011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d163012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d163012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d163013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d163013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d163020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52784 q ha hb
    | true =>
      simp only [d113858, d163020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52785 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d163021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d163021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d163022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d163022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d163048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52789 q ha hb
    | true =>
      simp only [d113894, d163048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52790 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d163049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d163049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d163054 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52791 q ha hb
    | true =>
      simp only [d113900, d163054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d163055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d163055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d163056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d163056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d163057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d163057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d163058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d163058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113908 q = 1) (hb : d163062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113908, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52793 q ha hb
    | true =>
      simp only [d113908, d163062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52794 q ha hb
  have h17 (q : Pattern) (ha : d113909 q = 1) (hb : d163063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113909, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113909, d163063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113910 q = 1) (hb : d163064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113910, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113910, d163064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113911 q = 1) (hb : d163065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113911, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113911, d163065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113914 q = 1) (hb : d163068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113914, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52795 q ha hb
    | true =>
      simp only [d113914, d163068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52796 q ha hb
  have h21 (q : Pattern) (ha : d113915 q = 1) (hb : d163069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113915, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113915, d163069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113916 q = 1) (hb : d163070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113916, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113916, d163070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113919 q = 1) (hb : d163073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52797 q ha hb
    | true =>
      simp only [d113919, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52798 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113920 q = 1) (hb : d163074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113920, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113922 q = 1) (hb : d163076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52799 q ha hb
    | true =>
      simp only [d113922, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113923 q = 1) (hb : d163077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113923, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113924 q = 1) (hb : d163078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113924, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113925 q = 1) (hb : d163079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113925, d163079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113926 q = 1) (hb : d163080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113926, d163080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113927 q = 1) (hb : d163081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113927, d163081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro52801 (p : Pattern) (ha : d113939 p = 1) (hb : d163093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113929 q = 1) (hb : d163083 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113929, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52790 q ha hb
    | true =>
      simp only [d113929, d163083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
  have h2 (q : Pattern) (ha : d113930 q = 1) (hb : d163084 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113930, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113930, d163084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113931 q = 1) (hb : d163085 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113931, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113931, d163085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113932 q = 1) (hb : d163086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113932, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113932, d163086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113933 q = 1) (hb : d163087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113933, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113933, d163087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113934 q = 1) (hb : d163088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
    | true =>
      simp only [d113934, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113935 q = 1) (hb : d163089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113936 q = 1) (hb : d163090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113936, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113937 q = 1) (hb : d163091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113938 q = 1) (hb : d163092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113939 q = 1) (hb : d163093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113939, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113939, d163093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52802 (p : Pattern) (ha : d113945 p = 1) (hb : d163099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113934 q = 1) (hb : d163088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
    | true =>
      simp only [d113934, d163088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113935 q = 1) (hb : d163089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d163089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113936 q = 1) (hb : d163090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113936, d163090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113937 q = 1) (hb : d163091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d163091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113938 q = 1) (hb : d163092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d163092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113940 q = 1) (hb : d163094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52780 q ha hb
    | true =>
      simp only [d113940, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113941 q = 1) (hb : d163095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113942 q = 1) (hb : d163096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113942, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113943 q = 1) (hb : d163097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113944 q = 1) (hb : d163098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113945 q = 1) (hb : d163099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113945, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113945, d163099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52803 (p : Pattern) (ha : d113952 p = 1) (hb : d163106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113919 q = 1) (hb : d163073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52797 q ha hb
    | true =>
      simp only [d113919, d163073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d163074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113920, d163074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113922 q = 1) (hb : d163076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52799 q ha hb
    | true =>
      simp only [d113922, d163076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113923 q = 1) (hb : d163077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113923, d163077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113924 q = 1) (hb : d163078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d163078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113950 q = 1) (hb : d163104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d163104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113951 q = 1) (hb : d163105 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d163105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113952 q = 1) (hb : d163106 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d163106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52804 (p : Pattern) (ha : d113954 p = 1) (hb : d163108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113940 q = 1) (hb : d163094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52780 q ha hb
    | true =>
      simp only [d113940, d163094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113941 q = 1) (hb : d163095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d163095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113942 q = 1) (hb : d163096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113942, d163096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113943 q = 1) (hb : d163097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d163097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113944 q = 1) (hb : d163098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d163098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113954 q = 1) (hb : d163108 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113954, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113954, d163108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52805 (p : Pattern) (ha : d76360 p = 1) (hb : d163124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53515 q = 1) (hb : d163123 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53515, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53515, d163123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d76360 q = 1) (hb : d163124 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d76360, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76360, d163124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52806 (p : Pattern) (ha : d113960 p = 1) (hb : d163114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17373 q = 1) (hb : d53504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17373, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113960 q = 1) (hb : d163114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113960, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113960, d163114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52807 (p : Pattern) (ha : d113961 p = 1) (hb : d163115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17380 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17380, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113961 q = 1) (hb : d163115 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113961, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113961, d163115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro52808 (p : Pattern) (ha : d113984 p = 1) (hb : d163133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113962 q = 1) (hb : d163116 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113962, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52806 q ha hb
    | true =>
      simp only [d113962, d163116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52807 q ha hb
  have h2 (q : Pattern) (ha : d113963 q = 1) (hb : d163117 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113963, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113963, d163117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113964 q = 1) (hb : d163118 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113964, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113964, d163118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113975 q = 1) (hb : d163119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113975, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52807 q ha hb
    | true =>
      simp only [d113975, d163119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46305 q hb ha
  have h5 (q : Pattern) (ha : d113976 q = 1) (hb : d163120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113976, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113976, d163120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113977 q = 1) (hb : d163121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113977, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113977, d163121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113978 q = 1) (hb : d163122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113978, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113978, d163122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113979 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52807 q ha hb
    | true =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
  have h9 (q : Pattern) (ha : d113980 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113981 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76367 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
    | true =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q hb ha
  have h12 (q : Pattern) (ha : d76368 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76369 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113982 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113983 q = 1) (hb : d163132 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113983, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113983, d163132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113984 q = 1) (hb : d163133 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113984, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113984, d163133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro52809 (p : Pattern) (ha : d113988 p = 1) (hb : d163138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113979 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52807 q ha hb
    | true =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
  have h2 (q : Pattern) (ha : d113980 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113981 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76367 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
    | true =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q hb ha
  have h5 (q : Pattern) (ha : d76368 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76369 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113982 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76370 q = 1) (hb : d163136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76370, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76370, d163136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113987 q = 1) (hb : d163137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113987, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113987, d163137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113988 q = 1) (hb : d163138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113988, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113988, d163138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro52810 (p : Pattern) (ha : d113994 p = 1) (hb : d163144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113985 q = 1) (hb : d163134 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113985, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52808 q ha hb
    | true =>
      simp only [d113985, d163134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113986 q = 1) (hb : d163135 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113986, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113986, d163135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113989 q = 1) (hb : d163139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52809 q ha hb
    | true =>
      simp only [d113989, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113990 q = 1) (hb : d163140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113991 q = 1) (hb : d163141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113991, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113991, d163141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113992 q = 1) (hb : d163142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113992, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113992, d163142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113993 q = 1) (hb : d163143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113993, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113993, d163143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113994 q = 1) (hb : d163144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113994, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113994, d163144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52811 (p : Pattern) (ha : d114001 p = 1) (hb : d163150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113996 q = 1) (hb : d163145 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113996, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
    | true =>
      simp only [d113996, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q hb ha
  have h2 (q : Pattern) (ha : d113997 q = 1) (hb : d163146 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113997, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113997, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113998 q = 1) (hb : d163147 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113998, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113998, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113999 q = 1) (hb : d163148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113999, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113999, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114000 q = 1) (hb : d163149 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114000, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114000, d163149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114001 q = 1) (hb : d163150 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114001, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114001, d163150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52812 (p : Pattern) (ha : d114007 p = 1) (hb : d163156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113989 q = 1) (hb : d163139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52809 q ha hb
    | true =>
      simp only [d113989, d163139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113990 q = 1) (hb : d163140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d163140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52811 q ha hb
    | true =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114004 q = 1) (hb : d163153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114004, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114004, d163153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114005 q = 1) (hb : d163154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114005, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114005, d163154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114006 q = 1) (hb : d163155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114006, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114006, d163155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114007 q = 1) (hb : d163156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114007, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114007, d163156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52813 (p : Pattern) (ha : d114010 p = 1) (hb : d163160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113979 q = 1) (hb : d163125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52807 q ha hb
    | true =>
      simp only [d113979, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
  have h2 (q : Pattern) (ha : d113980 q = 1) (hb : d163126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113981 q = 1) (hb : d163127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76367 q = 1) (hb : d163128 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
    | true =>
      simp only [d76367, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q hb ha
  have h5 (q : Pattern) (ha : d76368 q = 1) (hb : d163129 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76369 q = 1) (hb : d163130 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113982 q = 1) (hb : d163131 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113982, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113996 q = 1) (hb : d163145 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113996, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52805 q ha hb
    | true =>
      simp only [d113996, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q hb ha
  have h9 (q : Pattern) (ha : d113997 q = 1) (hb : d163146 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113997, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113997, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113998 q = 1) (hb : d163147 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113998, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113998, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113999 q = 1) (hb : d163148 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113999, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113999, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d114009 q = 1) (hb : d163159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114009, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114009, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114010 q = 1) (hb : d163160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114010, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d114010, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52814 (p : Pattern) (ha : d114026 p = 1) (hb : d163166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d163161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52813 q ha hb
    | true =>
      simp only [d114011, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d163162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114023 q = 1) (hb : d163163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114023, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114023, d163163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114024 q = 1) (hb : d163164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114024, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114024, d163164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114025 q = 1) (hb : d163165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114025, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114025, d163165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114026 q = 1) (hb : d163166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114026, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114026, d163166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52815 (p : Pattern) (ha : d114032 p = 1) (hb : d163172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114008 q = 1) (hb : d163157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114008, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52810 q ha hb
    | true =>
      simp only [d114008, d163157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52812 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114021 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d163158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114022, d163158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d114027 q = 1) (hb : d163167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114027, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52814 q ha hb
    | true =>
      simp only [d114027, d163167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114028 q = 1) (hb : d163168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114028, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114028, d163168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114029 q = 1) (hb : d163169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d163169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114030 q = 1) (hb : d163170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d163170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114031 q = 1) (hb : d163171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d163171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d114032 q = 1) (hb : d163172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d163172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52816 (p : Pattern) (ha : d114020 p = 1) (hb : d163177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114002 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52811 q ha hb
    | true =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114003 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114017 q = 1) (hb : d163174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114017, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114017, d163174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114018 q = 1) (hb : d163175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114018, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114018, d163175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114019 q = 1) (hb : d163176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114019, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114019, d163176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114020 q = 1) (hb : d163177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114020, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114020, d163177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52817 (p : Pattern) (ha : d114039 p = 1) (hb : d163183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114034 q = 1) (hb : d163178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114034, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52816 q ha hb
    | true =>
      simp only [d114034, d163178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114035 q = 1) (hb : d163179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114035, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114035, d163179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114036 q = 1) (hb : d163180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114036, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114036, d163180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114037 q = 1) (hb : d163181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114037, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114037, d163181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114038 q = 1) (hb : d163182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114038, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114038, d163182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114039 q = 1) (hb : d163183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114039, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114039, d163183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52818 (p : Pattern) (ha : d114045 p = 1) (hb : d163189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113831 q = 1) (hb : d162993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113831, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113831, d162993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52778 q ha hb
  have h2 (q : Pattern) (ha : d113832 q = 1) (hb : d162994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113832, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113832, d162994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113841 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113841, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52778 q ha hb
    | true =>
      simp only [d113841, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52781 q ha hb
  have h4 (q : Pattern) (ha : d113842 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113842, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113842, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113843 q = 1) (hb : d163005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113843, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113843, d163005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113928 q = 1) (hb : d163082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52792 q ha hb
    | true =>
      simp only [d113928, d163082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52800 q ha hb
  have h7 (q : Pattern) (ha : d113946 q = 1) (hb : d163100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113946, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52801 q ha hb
    | true =>
      simp only [d113946, d163100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52802 q ha hb
  have h8 (q : Pattern) (ha : d113947 q = 1) (hb : d163101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113947, d163101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113948 q = 1) (hb : d163102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113948, d163102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113949 q = 1) (hb : d163103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113949, d163103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113953 q = 1) (hb : d163107 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113953, d163107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52803 q ha hb
  have h12 (q : Pattern) (ha : d113955 q = 1) (hb : d163109 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113955, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113955, d163109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52804 q ha hb
  have h13 (q : Pattern) (ha : d113956 q = 1) (hb : d163110 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113956, d163110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113957 q = 1) (hb : d163111 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113957, d163111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113958 q = 1) (hb : d163112 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113958, d163112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113959 q = 1) (hb : d163113 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113959, d163113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d114033 q = 1) (hb : d163173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114033, d163173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52815 q ha hb
  have h18 (q : Pattern) (ha : d114040 q = 1) (hb : d163184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114040, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114040, d163184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52817 q ha hb
  have h19 (q : Pattern) (ha : d114041 q = 1) (hb : d163185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114041, d163185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d114042 q = 1) (hb : d163186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d114042, d163186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d114043 q = 1) (hb : d163187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d114043, d163187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d114044 q = 1) (hb : d163188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d114044, d163188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d114045 q = 1) (hb : d163189 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114045, d163189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro52819 (p : Pattern) (ha : d114051 p = 1) (hb : d163195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d163190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d163190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52818 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d163191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d163191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d163192 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d163192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d163193 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d163193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d163194 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d163194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d163195 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d163195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52820 (p : Pattern) (ha : d114057 p = 1) (hb : d163201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d162312 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52611 q ha hb
    | true =>
      simp only [d113073, d162312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52641 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d162464 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d162464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52671 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d162465 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d162465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d162709 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d162709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52721 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d162710 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d162710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d162711 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d162711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d162953 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d162953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52771 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d162954 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d162954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d162955 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d162955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d162956 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d162956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d163196 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d163196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52819 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d163197 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d163197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d163198 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d163198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d163199 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d163199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d163200 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d163200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d163201 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d163201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro52821 (p : Pattern) (ha : d114063 p = 1) (hb : d163207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d163202 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52820 q ha hb
    | true =>
      simp only [d114058, d163202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d163203 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d163203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d163204 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d163204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d163205 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d163205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d163206 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d163206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d163207 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d163207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52822 (p : Pattern) (ha : d114069 p = 1) (hb : d163213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d163208 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52821 q ha hb
    | true =>
      simp only [d114064, d163208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d163209 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d163209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d163210 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d163210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d163211 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d163211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d163212 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d163212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d163213 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d163213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52823 (p : Pattern) (ha : d114075 p = 1) (hb : d163219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d163214 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52822 q ha hb
    | true =>
      simp only [d114070, d163214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d163215 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d163215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d163216 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d163216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d163217 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d163217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d163218 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d163218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d163219 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d163219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52824 (p : Pattern) (ha : d114081 p = 1) (hb : d163225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d163220 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52823 q ha hb
    | true =>
      simp only [d114076, d163220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d163221 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d163221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d163222 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d163222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d163223 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d163223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d163224 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d163224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d163225 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d163225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52825 (p : Pattern) (ha : d114087 p = 1) (hb : d163231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d163226 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52824 q ha hb
    | true =>
      simp only [d114082, d163226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d163227 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d163227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d163228 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d163228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d163229 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d163229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d163230 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d163230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d163231 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d163231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52826 (p : Pattern) (ha : d114093 p = 1) (hb : d163237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d163232 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52825 q ha hb
    | true =>
      simp only [d114088, d163232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d163233 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d163233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d163234 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d163234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d163235 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d163235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d163236 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d163236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d163237 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d163237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52827 (p : Pattern) (ha : d114099 p = 1) (hb : d163243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d163238 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52826 q ha hb
    | true =>
      simp only [d114094, d163238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d163239 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d163239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d163240 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d163240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d163241 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d163241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d163242 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d163242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d163243 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d163243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52828 (p : Pattern) (ha : d53655 p = 1) (hb : d162092 p = 1) : d150329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d162092 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d162092 q = 1) : d12241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52285 q ha hb
    | true =>
      simp only [d204, d12241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d162092 q = 1) : d12292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d12292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d12292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d162092 q = 1) : d12293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d12293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d12293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d162092 q = 1) : d12294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d12294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d12294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d162092 q = 1) : d12295 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d12295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d12295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d162092 q = 1) : d150329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52829 (p : Pattern) (ha : d53665 p = 1) (hb : d162092 p = 1) : d150339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d162092 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d162092 q = 1) : d12268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d12268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52289 q ha hb
    | true =>
      simp only [d244, d12268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d162092 q = 1) : d150335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d162092 q = 1) : d150336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d162092 q = 1) : d150337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d162092 q = 1) : d150338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d162092 q = 1) : d150339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52830 (p : Pattern) (ha : d53671 p = 1) (hb : d162092 p = 1) : d150345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d162092 q = 1) : d12297 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d12297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52295 q ha hb
    | true =>
      simp only [d292, d12297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52296 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d162092 q = 1) : d12298 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d12298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d12298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d162092 q = 1) : d150327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d162092 q = 1) : d150328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d162092 q = 1) : d150330 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52828 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d162092 q = 1) : d150331 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d162092 q = 1) : d150332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d162092 q = 1) : d150333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d162092 q = 1) : d150334 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d162092 q = 1) : d150340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52829 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d162092 q = 1) : d150341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d162092 q = 1) : d150342 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d162092 q = 1) : d150343 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d162092 q = 1) : d150344 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d162092 q = 1) : d150345 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52831 (p : Pattern) (ha : d53677 p = 1) (hb : d162092 p = 1) : d150351 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d162092 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d162092 q = 1) : d150346 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52830 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d162092 q = 1) : d150347 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d162092 q = 1) : d150348 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d162092 q = 1) : d150349 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d162092 q = 1) : d150350 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d162092 q = 1) : d150351 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52832 (p : Pattern) (ha : d162092 p = 1) (hb : d171078 p = 1) : d163246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d162092 q = 1) : d162180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52329 q ha hb
    | true =>
      simp only [d16052, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52320 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d162092 q = 1) : d162181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d162092 q = 1) : d162182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d162092 q = 1) : d162183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d162092 q = 1) : d162184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171078 q = 1) : d163246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171078, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro52833 (p : Pattern) (ha : d162092 p = 1) (hb : d171089 p = 1) : d163257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171084 q = 1) : d163252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52355 q hb ha
    | true =>
      simp only [d171084, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52324 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171085 q = 1) : d163253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171085, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171086 q = 1) : d163254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171087 q = 1) : d163255 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171087, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171088 q = 1) : d163256 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171088, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171089 q = 1) : d163257 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171089, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52834 (p : Pattern) (ha : d162092 p = 1) (hb : d171095 p = 1) : d163263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d162092 q = 1) : d162186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52328 q ha hb
    | true =>
      simp only [d16058, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52330 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d162092 q = 1) : d162187 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171076 q = 1) : d163244 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171076, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171077 q = 1) : d163245 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171077, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171079 q = 1) : d163247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171079, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52832 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171080 q = 1) : d163248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171081 q = 1) : d163249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171082 q = 1) : d163250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171083 q = 1) : d163251 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171090 q = 1) : d163258 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171090, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52833 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171091 q = 1) : d163259 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171092 q = 1) : d163260 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171093 q = 1) : d163261 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171094 q = 1) : d163262 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171095 q = 1) : d163263 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52835 (p : Pattern) (ha : d162092 p = 1) (hb : d171101 p = 1) : d163269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171096 q = 1) : d163264 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171096, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52834 q ha hb
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171097 q = 1) : d163265 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171097, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171098 q = 1) : d163266 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171098, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171099 q = 1) : d163267 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171099, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171100 q = 1) : d163268 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171100, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171101 q = 1) : d163269 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171101, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52836 (p : Pattern) (ha : d162092 p = 1) (hb : d171105 p = 1) : d163273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d162092 q = 1) : d162331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52374 q ha hb
    | true =>
      simp only [d16249, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52363 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d162092 q = 1) : d162332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d162092 q = 1) : d162333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d162092 q = 1) : d162334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d162092 q = 1) : d162335 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171105 q = 1) : d163273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171105, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro52837 (p : Pattern) (ha : d162092 p = 1) (hb : d171116 p = 1) : d163284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171111 q = 1) : d163279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52401 q hb ha
    | true =>
      simp only [d171111, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52368 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171112 q = 1) : d163280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171112, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171113 q = 1) : d163281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171114 q = 1) : d163282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171114, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171115 q = 1) : d163283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171115, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171116 q = 1) : d163284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171116, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52838 (p : Pattern) (ha : d162092 p = 1) (hb : d171122 p = 1) : d163290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d162092 q = 1) : d162337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52373 q ha hb
    | true =>
      simp only [d16255, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52375 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d162092 q = 1) : d162338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171103 q = 1) : d163271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171103, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171104 q = 1) : d163272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171104, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171106 q = 1) : d163274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171106, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52836 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171107 q = 1) : d163275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171108 q = 1) : d163276 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171109 q = 1) : d163277 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171110 q = 1) : d163278 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171117 q = 1) : d163285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171117, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52837 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171118 q = 1) : d163286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171119 q = 1) : d163287 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171120 q = 1) : d163288 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171121 q = 1) : d163289 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171122 q = 1) : d163290 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52839 (p : Pattern) (ha : d162092 p = 1) (hb : d171128 p = 1) : d163296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171123 q = 1) : d163291 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171123, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52838 q ha hb
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171124 q = 1) : d163292 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171124, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171125 q = 1) : d163293 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171125, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171126 q = 1) : d163294 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171126, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171127 q = 1) : d163295 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171127, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171128 q = 1) : d163296 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171128, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52840 (p : Pattern) (ha : d162092 p = 1) (hb : d171133 p = 1) : d163301 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d162092 q = 1) : d162507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52415 q ha hb
    | true =>
      simp only [d16481, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52416 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d162092 q = 1) : d162508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d162092 q = 1) : d162509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d162092 q = 1) : d162510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d162092 q = 1) : d162511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171133 q = 1) : d163301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171133, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro52841 (p : Pattern) (ha : d162092 p = 1) (hb : d171140 p = 1) : d162673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d162092 q = 1) : d162638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52450 q ha hb
    | true =>
      simp only [d16673, d162638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d162092 q = 1) : d162639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d162639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d162092 q = 1) : d162640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d162640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d162092 q = 1) : d162641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16676, d162641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52448 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d162092 q = 1) : d162642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d162642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d162092 q = 1) : d162643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d162643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d162092 q = 1) : d162644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d162644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d162092 q = 1) : d162658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52424 q ha hb
    | true =>
      simp only [d16693, d162658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52423 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d162092 q = 1) : d162659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d162659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d162092 q = 1) : d162660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d162660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d162092 q = 1) : d162661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d162661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171139 q = 1) : d162672 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171139, d162672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171140 q = 1) : d162673 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171140, d162673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52842 (p : Pattern) (ha : d162092 p = 1) (hb : d171146 p = 1) : d163310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171141 q = 1) : d162674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52841 q ha hb
    | true =>
      simp only [d171141, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171142 q = 1) : d162675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171142, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d162092 q = 1) : d162664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52425 q ha hb
    | true =>
      simp only [d16699, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d162092 q = 1) : d162665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171143 q = 1) : d163307 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171144 q = 1) : d163308 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171145 q = 1) : d163309 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171146 q = 1) : d163310 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52843 (p : Pattern) (ha : d162092 p = 1) (hb : d171152 p = 1) : d163316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171147 q = 1) : d163311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52842 q ha hb
    | true =>
      simp only [d171147, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52426 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171148 q = 1) : d163312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171148, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171149 q = 1) : d163313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171150 q = 1) : d163314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171150, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171151 q = 1) : d163315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171151, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171152 q = 1) : d163316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171152, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52844 (p : Pattern) (ha : d162092 p = 1) (hb : d171158 p = 1) : d163322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d162092 q = 1) : d162513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52414 q ha hb
    | true =>
      simp only [d16487, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52417 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d162092 q = 1) : d162514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171131 q = 1) : d163299 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171131, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171132 q = 1) : d163300 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171132, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171134 q = 1) : d163302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171134, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52840 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171135 q = 1) : d163303 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171136 q = 1) : d163304 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171137 q = 1) : d163305 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171138 q = 1) : d163306 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171153 q = 1) : d163317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171153, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52843 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171154 q = 1) : d163318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171155 q = 1) : d163319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171156 q = 1) : d163320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171157 q = 1) : d163321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171158 q = 1) : d163322 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52845 (p : Pattern) (ha : d162092 p = 1) (hb : d171164 p = 1) : d163328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171159 q = 1) : d163323 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171159, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52844 q ha hb
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171160 q = 1) : d163324 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171160, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171161 q = 1) : d163325 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171161, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171162 q = 1) : d163326 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171162, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171163 q = 1) : d163327 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171163, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171164 q = 1) : d163328 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171164, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52846 (p : Pattern) (ha : d162092 p = 1) (hb : d171170 p = 1) : d163334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d162092 q = 1) : d162753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52470 q ha hb
    | true =>
      simp only [d16833, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52471 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d162092 q = 1) : d162754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d162092 q = 1) : d162755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d162092 q = 1) : d162756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d162092 q = 1) : d162757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171170 q = 1) : d163334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171170, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro52847 (p : Pattern) (ha : d162092 p = 1) (hb : d171177 p = 1) : d162917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d162092 q = 1) : d162882 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52505 q ha hb
    | true =>
      simp only [d17033, d162882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d162092 q = 1) : d162883 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d162883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d162092 q = 1) : d162884 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d162884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d162092 q = 1) : d162885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17036, d162885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52503 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d162092 q = 1) : d162886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d162886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d162092 q = 1) : d162887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d162887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d162092 q = 1) : d162888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d162888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d162092 q = 1) : d162902 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52479 q ha hb
    | true =>
      simp only [d17053, d162902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52478 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d162092 q = 1) : d162903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d162903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d162092 q = 1) : d162904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d162904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d162092 q = 1) : d162905 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d162905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171176 q = 1) : d162916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171176, d162916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171177 q = 1) : d162917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171177, d162917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52848 (p : Pattern) (ha : d162092 p = 1) (hb : d171183 p = 1) : d163343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171178 q = 1) : d162918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52847 q ha hb
    | true =>
      simp only [d171178, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171179 q = 1) : d162919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171179, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d162092 q = 1) : d162908 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52480 q ha hb
    | true =>
      simp only [d17059, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d162092 q = 1) : d162909 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171180 q = 1) : d163340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171181 q = 1) : d163341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171182 q = 1) : d163342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171183 q = 1) : d163343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52849 (p : Pattern) (ha : d162092 p = 1) (hb : d171189 p = 1) : d163349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171184 q = 1) : d163344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52848 q ha hb
    | true =>
      simp only [d171184, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52481 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171185 q = 1) : d163345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171185, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171186 q = 1) : d163346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171187 q = 1) : d163347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171187, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171188 q = 1) : d163348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171188, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171189 q = 1) : d163349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171189, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52850 (p : Pattern) (ha : d162092 p = 1) (hb : d171195 p = 1) : d163355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d162092 q = 1) : d162759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52469 q ha hb
    | true =>
      simp only [d16839, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52472 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d162092 q = 1) : d162760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171168 q = 1) : d163332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171168, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171169 q = 1) : d163333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171169, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171171 q = 1) : d163335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171171, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52846 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171172 q = 1) : d163336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171173 q = 1) : d163337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171174 q = 1) : d163338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171175 q = 1) : d163339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171190 q = 1) : d163350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171190, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52849 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171191 q = 1) : d163351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171192 q = 1) : d163352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171193 q = 1) : d163353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171194 q = 1) : d163354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171195 q = 1) : d163355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52851 (p : Pattern) (ha : d162092 p = 1) (hb : d171201 p = 1) : d163361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171196 q = 1) : d163356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171196, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52850 q ha hb
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171197 q = 1) : d163357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171197, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171198 q = 1) : d163358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171198, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171199 q = 1) : d163359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171199, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171200 q = 1) : d163360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171200, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171201 q = 1) : d163361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171201, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52852 (p : Pattern) (ha : d162092 p = 1) (hb : d171208 p = 1) : d163368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d162092 q = 1) : d162997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52525 q ha hb
    | true =>
      simp only [d17199, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52526 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d162092 q = 1) : d162998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d162092 q = 1) : d162999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d162092 q = 1) : d163000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d162092 q = 1) : d163001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171208 q = 1) : d163368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171208, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro52853 (p : Pattern) (ha : d162092 p = 1) (hb : d171215 p = 1) : d163160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d162092 q = 1) : d163125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52560 q ha hb
    | true =>
      simp only [d17397, d163125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d162092 q = 1) : d163126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d163126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d162092 q = 1) : d163127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d163127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d162092 q = 1) : d163128 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17400, d163128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52558 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d162092 q = 1) : d163129 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d163129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d162092 q = 1) : d163130 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d163130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d162092 q = 1) : d163131 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d163131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d162092 q = 1) : d163145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52534 q ha hb
    | true =>
      simp only [d17417, d163145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52533 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d162092 q = 1) : d163146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d163146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d162092 q = 1) : d163147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d163147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d162092 q = 1) : d163148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d163148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171214 q = 1) : d163159 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171214, d163159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171215 q = 1) : d163160 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171215, d163160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro52854 (p : Pattern) (ha : d162092 p = 1) (hb : d171221 p = 1) : d163377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171216 q = 1) : d163161 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52853 q ha hb
    | true =>
      simp only [d171216, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171217 q = 1) : d163162 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171217, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d162092 q = 1) : d163151 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52535 q ha hb
    | true =>
      simp only [d17423, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d162092 q = 1) : d163152 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171218 q = 1) : d163374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171219 q = 1) : d163375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171220 q = 1) : d163376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171221 q = 1) : d163377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52855 (p : Pattern) (ha : d162092 p = 1) (hb : d171227 p = 1) : d163383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171222 q = 1) : d163378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52854 q ha hb
    | true =>
      simp only [d171222, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52536 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171223 q = 1) : d163379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171223, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171224 q = 1) : d163380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171225 q = 1) : d163381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171225, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171226 q = 1) : d163382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171226, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171227 q = 1) : d163383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171227, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52856 (p : Pattern) (ha : d162092 p = 1) (hb : d171233 p = 1) : d163389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d162092 q = 1) : d163003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52524 q ha hb
    | true =>
      simp only [d17205, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52527 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d162092 q = 1) : d163004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171206 q = 1) : d163366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171206, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171207 q = 1) : d163367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171207, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171209 q = 1) : d163369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171209, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52852 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171210 q = 1) : d163370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171211 q = 1) : d163371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171212 q = 1) : d163372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171213 q = 1) : d163373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171228 q = 1) : d163384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171228, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52855 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171229 q = 1) : d163385 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171230 q = 1) : d163386 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171231 q = 1) : d163387 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171232 q = 1) : d163388 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171233 q = 1) : d163389 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52857 (p : Pattern) (ha : d162092 p = 1) (hb : d171239 p = 1) : d163395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171234 q = 1) : d163390 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171234, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52856 q ha hb
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171235 q = 1) : d163391 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171235, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171236 q = 1) : d163392 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171236, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171237 q = 1) : d163393 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171237, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171238 q = 1) : d163394 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171238, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171239 q = 1) : d163395 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171239, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52858 (p : Pattern) (ha : d162092 p = 1) (hb : d171245 p = 1) : d163401 p = 1 := by
  have h0 (q : Pattern) (ha : d162092 q = 1) (hb : d171102 q = 1) : d163270 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52831 q hb ha
    | true =>
      simp only [d171102, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52835 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171129 q = 1) : d163297 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171129, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52839 q ha hb
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171130 q = 1) : d163298 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171165 q = 1) : d163329 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171165, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52845 q ha hb
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171166 q = 1) : d163330 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171166, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171167 q = 1) : d163331 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d162092 q = 1) (hb : d171202 q = 1) : d163362 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171202, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52851 q ha hb
  have h8 (q : Pattern) (ha : d162092 q = 1) (hb : d171203 q = 1) : d163363 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171203, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d162092 q = 1) (hb : d171204 q = 1) : d163364 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171204, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d162092 q = 1) (hb : d171205 q = 1) : d163365 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d162092 q = 1) (hb : d171240 q = 1) : d163396 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171240, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52857 q ha hb
  have h12 (q : Pattern) (ha : d162092 q = 1) (hb : d171241 q = 1) : d163397 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171241, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d162092 q = 1) (hb : d171242 q = 1) : d163398 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171242, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d162092 q = 1) (hb : d171243 q = 1) : d163399 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171243, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d162092 q = 1) (hb : d171244 q = 1) : d163400 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d162092 q = 1) (hb : d171245 q = 1) : d163401 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro52859 (p : Pattern) (ha : d162092 p = 1) (hb : d171251 p = 1) : d163407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171246 q = 1) : d163402 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52858 q ha hb
    | true =>
      simp only [d171246, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171247 q = 1) : d163403 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171248 q = 1) : d163404 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171249 q = 1) : d163405 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171250 q = 1) : d163406 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171251 q = 1) : d163407 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52860 (p : Pattern) (ha : d162092 p = 1) (hb : d171257 p = 1) : d163413 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171252 q = 1) : d163408 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52859 q ha hb
    | true =>
      simp only [d171252, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171253 q = 1) : d163409 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171254 q = 1) : d163410 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171255 q = 1) : d163411 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171256 q = 1) : d163412 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162092 q = 1) (hb : d171257 q = 1) : d163413 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52861 (p : Pattern) (ha : d162095 p = 1) (hb : d171263 p = 1) : d163419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162092 q = 1) (hb : d171258 q = 1) : d163414 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52860 q ha hb
    | true =>
      simp only [d171258, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162092 q = 1) (hb : d171259 q = 1) : d163415 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162092 q = 1) (hb : d171260 q = 1) : d163416 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162092 q = 1) (hb : d171261 q = 1) : d163417 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162092 q = 1) (hb : d171262 q = 1) : d163418 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d162095 q = 1) (hb : d171263 q = 1) : d163419 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d162095, d171263, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d162095, d171263, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro52862 (p : Pattern) (ha : d162095 p = 1) (hb : d171269 p = 1) : d163425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162095 q = 1) (hb : d171264 q = 1) : d163420 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52861 q ha hb
    | true =>
      simp only [d171264, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162095 q = 1) (hb : d171265 q = 1) : d163421 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162095 q = 1) (hb : d171266 q = 1) : d163422 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162095 q = 1) (hb : d171267 q = 1) : d163423 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162095 q = 1) (hb : d171268 q = 1) : d163424 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162095 q = 1) (hb : d171269 q = 1) : d163425 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52863 (p : Pattern) (ha : d162095 p = 1) (hb : d171275 p = 1) : d163431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162095 q = 1) (hb : d171270 q = 1) : d163426 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52862 q ha hb
    | true =>
      simp only [d171270, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162095 q = 1) (hb : d171271 q = 1) : d163427 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162095 q = 1) (hb : d171272 q = 1) : d163428 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162095 q = 1) (hb : d171273 q = 1) : d163429 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162095 q = 1) (hb : d171274 q = 1) : d163430 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162095 q = 1) (hb : d171275 q = 1) : d163431 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52864 (p : Pattern) (ha : d162095 p = 1) (hb : d171281 p = 1) : d163437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162095 q = 1) (hb : d171276 q = 1) : d163432 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52863 q ha hb
    | true =>
      simp only [d171276, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162095 q = 1) (hb : d171277 q = 1) : d163433 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162095 q = 1) (hb : d171278 q = 1) : d163434 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162095 q = 1) (hb : d171279 q = 1) : d163435 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162095 q = 1) (hb : d171280 q = 1) : d163436 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162095 q = 1) (hb : d171281 q = 1) : d163437 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52865 (p : Pattern) (ha : d162095 p = 1) (hb : d171287 p = 1) : d163443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d162095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d162095 q = 1) (hb : d171282 q = 1) : d163438 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52864 q ha hb
    | true =>
      simp only [d171282, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d162095 q = 1) (hb : d171283 q = 1) : d163439 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d162095 q = 1) (hb : d171284 q = 1) : d163440 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d162095 q = 1) (hb : d171285 q = 1) : d163441 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d162095 q = 1) (hb : d171286 q = 1) : d163442 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d162095 q = 1) (hb : d171287 q = 1) : d163443 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52866 (p : Pattern) (ha : d12289 p = 1) (hb : d112800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d12285 q = 1) (hb : d112790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d112790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12285, d112790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12286 q = 1) (hb : d112797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d112797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12286, d112797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12287 q = 1) (hb : d112798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d112798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12287, d112798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12288 q = 1) (hb : d112799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d112799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12288, d112799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12289 q = 1) (hb : d112800 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d112800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d112800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52867 (p : Pattern) (ha : d12296 p = 1) (hb : d112819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52580 q ha hb
    | true =>
      simp only [d12234, d112698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d12285 q = 1) (hb : d112790 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d112790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12285, d112790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12286 q = 1) (hb : d112797 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d112797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12286, d112797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12287 q = 1) (hb : d112798 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d112798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12287, d112798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12288 q = 1) (hb : d112799 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d112799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d112799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112805 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112809 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12241 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q ha hb
    | true =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d12292 q = 1) (hb : d112812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d112812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12292, d112812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12293 q = 1) (hb : d112816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d112816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12293, d112816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12294 q = 1) (hb : d112817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d112817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12294, d112817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12295 q = 1) (hb : d112818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d112818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12295, d112818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12296 q = 1) (hb : d112819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d112819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12296, d112819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52868 (p : Pattern) (ha : d112828 p = 1) (hb : d150329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52582 q ha hb
    | true =>
      simp only [d12241, d112705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d112812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d112812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12292, d112812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12293 q = 1) (hb : d112816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d112816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d112816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12294 q = 1) (hb : d112826 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d112826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d112826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12295 q = 1) (hb : d112827 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d112827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d112827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112828 q = 1) (hb : d150329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52869 (p : Pattern) (ha : d112858 p = 1) (hb : d150339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d112732 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d112732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52586 q ha hb
    | true =>
      simp only [d12268, d112732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d150335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112848, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112854 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112855 q = 1) (hb : d150336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112856 q = 1) (hb : d150337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112857 q = 1) (hb : d150338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112858 q = 1) (hb : d150339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52870 (p : Pattern) (ha : d112864 p = 1) (hb : d150345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d112820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d112820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52866 q ha hb
    | true =>
      simp only [d12297, d112820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52867 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12298 q = 1) (hb : d112823 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d112823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d112823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112824 q = 1) (hb : d150327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112824, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112825 q = 1) (hb : d150328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112825, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112829 q = 1) (hb : d150330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112829, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52868 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112830 q = 1) (hb : d150331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112830, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112831 q = 1) (hb : d150332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112831, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d112832 q = 1) (hb : d150333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112832, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d112833 q = 1) (hb : d150334 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112833, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112859 q = 1) (hb : d150340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112859, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52869 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112860 q = 1) (hb : d150341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112860, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112861 q = 1) (hb : d150342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112861, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d112862 q = 1) (hb : d150343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112862, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d112863 q = 1) (hb : d150344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112863, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d112864 q = 1) (hb : d150345 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112864, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52871 (p : Pattern) (ha : d112870 p = 1) (hb : d150351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d112744 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18822 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d112745 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d112746 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d112747 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d112748 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112865 q = 1) (hb : d150346 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112865, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52870 q ha hb
  have h8 (q : Pattern) (ha : d112866 q = 1) (hb : d150347 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112866, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112867 q = 1) (hb : d150348 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112867, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112868 q = 1) (hb : d150349 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112868, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112869 q = 1) (hb : d150350 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112869, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112870 q = 1) (hb : d150351 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d112870, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro52872 (p : Pattern) (ha : d112954 p = 1) (hb : d162176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112887 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
    | true =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h5 (q : Pattern) (ha : d112944 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112944, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112951 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112951, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112952 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112952, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112953 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112953, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112954 q = 1) (hb : d162176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52873 (p : Pattern) (ha : d112975 p = 1) (hb : d162185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112887 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52613 q ha hb
    | true =>
      simp only [d112887, d162171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18555 q hb ha
  have h4 (q : Pattern) (ha : d112944 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112944, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112951 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112951, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112952 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112952, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112953 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112953, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112960 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d112897 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52615 q ha hb
    | true =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q hb ha
  have h13 (q : Pattern) (ha : d112968 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d112968, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112972 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112972, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112973 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d112973, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112974 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d112974, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112975 q = 1) (hb : d162185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112975, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52874 (p : Pattern) (ha : d112995 p = 1) (hb : d163246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112897 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52615 q ha hb
    | true =>
      simp only [d112897, d162180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18556 q hb ha
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112968, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112972 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112993 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112994 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112995 q = 1) (hb : d163246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52875 (p : Pattern) (ha : d113053 p = 1) (hb : d163257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113042 q = 1) (hb : d163252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113042, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52637 q ha hb
    | true =>
      simp only [d113042, d163252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18560 q hb ha
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d163253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113043, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113050 q = 1) (hb : d163254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113051 q = 1) (hb : d163255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113052 q = 1) (hb : d163256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113053 q = 1) (hb : d163257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52876 (p : Pattern) (ha : d113066 p = 1) (hb : d163263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112976 q = 1) (hb : d162186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52872 q ha hb
    | true =>
      simp only [d112976, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52873 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112990 q = 1) (hb : d162187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112990, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112991 q = 1) (hb : d163244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112991, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112992 q = 1) (hb : d163245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112992, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112996 q = 1) (hb : d163247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112996, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52874 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112998 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112999 q = 1) (hb : d163248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112999, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113000 q = 1) (hb : d163249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113000, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113001 q = 1) (hb : d163250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113001, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113002 q = 1) (hb : d163251 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113002, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113054 q = 1) (hb : d163258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113054, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52875 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113062 q = 1) (hb : d163259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113062, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113063 q = 1) (hb : d163260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113063, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113064 q = 1) (hb : d163261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113064, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113065 q = 1) (hb : d163262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113065, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113066 q = 1) (hb : d163263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113066, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52877 (p : Pattern) (ha : d113072 p = 1) (hb : d163269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d163264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52876 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d163265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d163266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d163267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d163268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d163269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52878 (p : Pattern) (ha : d113161 p = 1) (hb : d162327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113094 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
    | true =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h5 (q : Pattern) (ha : d113151 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113151, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113158 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113158, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113159 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113159, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113160 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113160, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113161 q = 1) (hb : d162327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52879 (p : Pattern) (ha : d113182 p = 1) (hb : d162336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113094 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52643 q ha hb
    | true =>
      simp only [d113094, d162322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18595 q hb ha
  have h4 (q : Pattern) (ha : d113151 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113151, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113158 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113158, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113159 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113159, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113160 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113160, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113167 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113172 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113104 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52645 q ha hb
    | true =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q hb ha
  have h13 (q : Pattern) (ha : d113175 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113175, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113179 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113179, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113180 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113180, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113181 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113181, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113182 q = 1) (hb : d162336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113182, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52880 (p : Pattern) (ha : d113202 p = 1) (hb : d163273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113104 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52645 q ha hb
    | true =>
      simp only [d113104, d162331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18596 q hb ha
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113175, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113179 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113200 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113201 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113202 q = 1) (hb : d163273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52881 (p : Pattern) (ha : d113264 p = 1) (hb : d163284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113253 q = 1) (hb : d163279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113253, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52667 q ha hb
    | true =>
      simp only [d113253, d163279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18600 q hb ha
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d163280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113254, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113260 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113261 q = 1) (hb : d163281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113262 q = 1) (hb : d163282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113263 q = 1) (hb : d163283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113264 q = 1) (hb : d163284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52882 (p : Pattern) (ha : d113277 p = 1) (hb : d163290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113183 q = 1) (hb : d162337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52878 q ha hb
    | true =>
      simp only [d113183, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52879 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113196 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113197 q = 1) (hb : d162338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113197, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113198 q = 1) (hb : d163271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113198, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113199 q = 1) (hb : d163272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113199, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113203 q = 1) (hb : d163274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113203, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52880 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113205 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113206 q = 1) (hb : d163275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113206, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113207 q = 1) (hb : d163276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113207, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113208 q = 1) (hb : d163277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113208, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113209 q = 1) (hb : d163278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113209, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113265 q = 1) (hb : d163285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113265, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52881 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113272 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113273 q = 1) (hb : d163286 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113273, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113274 q = 1) (hb : d163287 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113274, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113275 q = 1) (hb : d163288 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113275, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113276 q = 1) (hb : d163289 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113276, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113277 q = 1) (hb : d163290 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113277, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52883 (p : Pattern) (ha : d113283 p = 1) (hb : d163296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d163291 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52882 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d163292 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d163293 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d163294 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d163295 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d163296 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52884 (p : Pattern) (ha : d113392 p = 1) (hb : d162502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113312 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52676 q ha hb
    | true =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
  have h5 (q : Pattern) (ha : d113382 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113382, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113389 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113389, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113390 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113390, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113391 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113391, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113392 q = 1) (hb : d162502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52885 (p : Pattern) (ha : d113414 p = 1) (hb : d162512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113312 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52676 q ha hb
    | true =>
      simp only [d113312, d162497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52677 q ha hb
  have h4 (q : Pattern) (ha : d113382 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113382, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113389 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113389, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113390 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113390, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113391 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113391, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113403 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113322 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52679 q ha hb
    | true =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52680 q ha hb
  have h13 (q : Pattern) (ha : d113407 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113407, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113411 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113411, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113412 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113412, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113413 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113413, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113414 q = 1) (hb : d162512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113414, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52886 (p : Pattern) (ha : d113439 p = 1) (hb : d163301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113322 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52679 q ha hb
    | true =>
      simp only [d113322, d162507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52680 q ha hb
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113407, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113411 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113437 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113438 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113439 q = 1) (hb : d163301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52887 (p : Pattern) (ha : d113503 p = 1) (hb : d163310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d162674 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52715 q ha hb
    | true =>
      simp only [d113498, d162674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d162675 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d162675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113489 q = 1) (hb : d162664 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52713 q ha hb
    | true =>
      simp only [d113489, d162664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113490 q = 1) (hb : d162665 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d162665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113500 q = 1) (hb : d163307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113500, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113500, d163307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113501 q = 1) (hb : d163308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113501, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113501, d163308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113502 q = 1) (hb : d163309 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113502, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113502, d163309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113503 q = 1) (hb : d163310 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113503, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113503, d163310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52888 (p : Pattern) (ha : d113519 p = 1) (hb : d163316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113508 q = 1) (hb : d163311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113508, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52887 q ha hb
    | true =>
      simp only [d113508, d163311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52718 q ha hb
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d163312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113509, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113516 q = 1) (hb : d163313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113517 q = 1) (hb : d163314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113518 q = 1) (hb : d163315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113519 q = 1) (hb : d163316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52889 (p : Pattern) (ha : d113532 p = 1) (hb : d163322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113415 q = 1) (hb : d162513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52884 q ha hb
    | true =>
      simp only [d113415, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52885 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113434 q = 1) (hb : d162514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113434, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113435 q = 1) (hb : d163299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113435, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113436 q = 1) (hb : d163300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113436, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113440 q = 1) (hb : d163302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113440, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52886 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113442 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113443 q = 1) (hb : d163303 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113443, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113444 q = 1) (hb : d163304 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113444, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113445 q = 1) (hb : d163305 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113445, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113446 q = 1) (hb : d163306 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113446, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113520 q = 1) (hb : d163317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113520, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52888 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113528 q = 1) (hb : d163318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113528, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113529 q = 1) (hb : d163319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113529, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113530 q = 1) (hb : d163320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113530, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113531 q = 1) (hb : d163321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113531, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113532 q = 1) (hb : d163322 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113532, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52890 (p : Pattern) (ha : d113538 p = 1) (hb : d163328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d163323 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52889 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d163324 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d163325 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d163326 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d163327 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d163328 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52891 (p : Pattern) (ha : d113648 p = 1) (hb : d162748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113568 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52726 q ha hb
    | true =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
  have h5 (q : Pattern) (ha : d113638 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113638, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113645 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113645, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113646 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113646, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113647 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113647, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113648 q = 1) (hb : d162748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52892 (p : Pattern) (ha : d113670 p = 1) (hb : d162758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113568 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52726 q ha hb
    | true =>
      simp only [d113568, d162743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52727 q ha hb
  have h4 (q : Pattern) (ha : d113638 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113638, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113645 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113645, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113646 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113646, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113647 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113647, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113659 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113578 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52729 q ha hb
    | true =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52730 q ha hb
  have h13 (q : Pattern) (ha : d113663 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113663, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113667 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113667, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113668 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113668, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113669 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113669, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113670 q = 1) (hb : d162758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113670, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52893 (p : Pattern) (ha : d113695 p = 1) (hb : d163334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113578 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52729 q ha hb
    | true =>
      simp only [d113578, d162753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52730 q ha hb
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113663, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113667 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113693 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113694 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113695 q = 1) (hb : d163334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52894 (p : Pattern) (ha : d113759 p = 1) (hb : d163343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d162918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52765 q ha hb
    | true =>
      simp only [d113754, d162918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d162919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d162919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d162908 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52763 q ha hb
    | true =>
      simp only [d113745, d162908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d162909 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d162909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113756 q = 1) (hb : d163340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113756, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113756, d163340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113757 q = 1) (hb : d163341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113757, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113757, d163341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113758 q = 1) (hb : d163342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113758, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113758, d163342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113759 q = 1) (hb : d163343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113759, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113759, d163343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52895 (p : Pattern) (ha : d113775 p = 1) (hb : d163349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113764 q = 1) (hb : d163344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113764, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52894 q ha hb
    | true =>
      simp only [d113764, d163344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52768 q ha hb
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d163345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113765, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113772 q = 1) (hb : d163346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113773 q = 1) (hb : d163347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113774 q = 1) (hb : d163348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113775 q = 1) (hb : d163349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52896 (p : Pattern) (ha : d113788 p = 1) (hb : d163355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113671 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52891 q ha hb
    | true =>
      simp only [d113671, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52892 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113690 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113690, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113691 q = 1) (hb : d163332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113691, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113692 q = 1) (hb : d163333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113692, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113696 q = 1) (hb : d163335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113696, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52893 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113698 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113699 q = 1) (hb : d163336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113699, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113700 q = 1) (hb : d163337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113700, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113701 q = 1) (hb : d163338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113701, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113702 q = 1) (hb : d163339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113702, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113776 q = 1) (hb : d163350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113776, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52895 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113783 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113784 q = 1) (hb : d163351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113784, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113785 q = 1) (hb : d163352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113785, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113786 q = 1) (hb : d163353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113786, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113787 q = 1) (hb : d163354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113787, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113788 q = 1) (hb : d163355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113788, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52897 (p : Pattern) (ha : d113794 p = 1) (hb : d163361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d163356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52896 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d163357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d163358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d163359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d163360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d163361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52898 (p : Pattern) (ha : d113905 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113825 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52776 q ha hb
    | true =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
  have h5 (q : Pattern) (ha : d113895 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113895, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113902 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113902, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113903 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113903, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113904 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113904, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113905 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52899 (p : Pattern) (ha : d113927 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113825 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52776 q ha hb
    | true =>
      simp only [d113825, d162987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52777 q ha hb
  have h4 (q : Pattern) (ha : d113895 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113895, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113902 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113902, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113903 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113903, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113904 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113904, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113911 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113916 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113835 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52779 q ha hb
    | true =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52780 q ha hb
  have h13 (q : Pattern) (ha : d113920 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113920, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113924 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113924, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113925 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113925, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113926 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113926, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113927 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113927, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52900 (p : Pattern) (ha : d113952 p = 1) (hb : d163368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113835 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52779 q ha hb
    | true =>
      simp only [d113835, d162997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52780 q ha hb
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113920, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113924 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113950 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113951 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113952 q = 1) (hb : d163368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52901 (p : Pattern) (ha : d114016 p = 1) (hb : d163377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d163161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52813 q ha hb
    | true =>
      simp only [d114011, d163161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d163162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d163162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d163151 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52811 q ha hb
    | true =>
      simp only [d114002, d163151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d163152 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d163152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114013 q = 1) (hb : d163374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114013, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114013, d163374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114014 q = 1) (hb : d163375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114014, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114014, d163375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114015 q = 1) (hb : d163376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114015, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114015, d163376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114016 q = 1) (hb : d163377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114016, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114016, d163377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro52902 (p : Pattern) (ha : d114032 p = 1) (hb : d163383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d114008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d114021 q = 1) (hb : d163378 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114021, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52901 q ha hb
    | true =>
      simp only [d114021, d163378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52816 q ha hb
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d163379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114022, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d114029 q = 1) (hb : d163380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d114030 q = 1) (hb : d163381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114031 q = 1) (hb : d163382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114032 q = 1) (hb : d163383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52903 (p : Pattern) (ha : d114045 p = 1) (hb : d163389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113928 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52898 q ha hb
    | true =>
      simp only [d113928, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52899 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113947 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113947, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113948 q = 1) (hb : d163366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113948, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113949 q = 1) (hb : d163367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113949, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113953 q = 1) (hb : d163369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113953, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52900 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113955 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113956 q = 1) (hb : d163370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113956, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113957 q = 1) (hb : d163371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113957, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113958 q = 1) (hb : d163372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113958, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113959 q = 1) (hb : d163373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113959, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114033 q = 1) (hb : d163384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d114033, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52902 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d114040 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d114041 q = 1) (hb : d163385 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d114041, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d114042 q = 1) (hb : d163386 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114042, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d114043 q = 1) (hb : d163387 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114043, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d114044 q = 1) (hb : d163388 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114044, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d114045 q = 1) (hb : d163389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d114045, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52904 (p : Pattern) (ha : d114051 p = 1) (hb : d163395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d163390 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52903 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d163391 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d163392 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d163393 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d163394 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d163395 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52905 (p : Pattern) (ha : d114057 p = 1) (hb : d163401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d163270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52871 q ha hb
    | true =>
      simp only [d113073, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52877 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d163297 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52883 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d163298 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d163329 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52890 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d163330 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d163331 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d163362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52897 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d163363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d163364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d163365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d163396 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52904 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d163397 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d163398 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d163399 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d163400 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d163401 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro52906 (p : Pattern) (ha : d114063 p = 1) (hb : d163407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d163402 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52905 q ha hb
    | true =>
      simp only [d114058, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d163403 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d163404 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d163405 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d163406 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d163407 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52907 (p : Pattern) (ha : d114069 p = 1) (hb : d163413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d163408 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52906 q ha hb
    | true =>
      simp only [d114064, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d163409 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d163410 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d163411 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d163412 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d163413 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52908 (p : Pattern) (ha : d114075 p = 1) (hb : d163419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d163414 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52907 q ha hb
    | true =>
      simp only [d114070, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d163415 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d163416 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d163417 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d163418 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d163419 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52909 (p : Pattern) (ha : d114081 p = 1) (hb : d163425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d163420 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52908 q ha hb
    | true =>
      simp only [d114076, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d163421 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d163422 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d163423 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d163424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d163425 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52910 (p : Pattern) (ha : d114087 p = 1) (hb : d163431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d163426 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52909 q ha hb
    | true =>
      simp only [d114082, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d163427 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d163428 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d163429 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d163430 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d163431 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52911 (p : Pattern) (ha : d114093 p = 1) (hb : d163437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d163432 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52910 q ha hb
    | true =>
      simp only [d114088, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d163433 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d163434 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d163435 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d163436 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d163437 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52912 (p : Pattern) (ha : d114099 p = 1) (hb : d163443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d163438 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52911 q ha hb
    | true =>
      simp only [d114094, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d163439 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d163440 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d163441 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d163442 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d163443 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro52913 (p : Pattern) (ha : d12289 p = 1) (hb : d115280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12234 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12285 q = 1) (hb : d115276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d115276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12285, d115276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12286 q = 1) (hb : d115277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d115277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12286, d115277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12287 q = 1) (hb : d115278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d115278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12287, d115278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12288 q = 1) (hb : d115279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d115279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12288, d115279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12289 q = 1) (hb : d115280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d115280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d115280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52914 (p : Pattern) (ha : d12296 p = 1) (hb : d115285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12234 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12285 q = 1) (hb : d115276 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d115276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12285, d115276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12286 q = 1) (hb : d115277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d115277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12286, d115277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12287 q = 1) (hb : d115278 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d115278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12287, d115278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12288 q = 1) (hb : d115279 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d115279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d115279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12355 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d12241 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12292 q = 1) (hb : d115281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d115281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12292, d115281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12293 q = 1) (hb : d115282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d115282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12293, d115282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12294 q = 1) (hb : d115283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d115283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12294, d115283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12295 q = 1) (hb : d115284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d115284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12295, d115284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d12296 q = 1) (hb : d115285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d115285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12296, d115285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52915 (p : Pattern) (ha : d115292 p = 1) (hb : d150329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12241 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d115281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d115281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12292, d115281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12293 q = 1) (hb : d115282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d115282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d115282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12294 q = 1) (hb : d115290 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d115290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d115290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12295 q = 1) (hb : d115291 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d115291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d115291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d150329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d150329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro52916 (p : Pattern) (ha : d115302 p = 1) (hb : d150339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12399 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12268 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115298 q = 1) (hb : d150335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115298, d150335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d150336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115299, d150336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d150337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d150337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d150338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d150338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d150339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d150339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52917 (p : Pattern) (ha : d115308 p = 1) (hb : d150345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d115286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d115286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52913 q ha hb
    | true =>
      simp only [d12297, d115286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52914 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12298 q = 1) (hb : d115287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d115287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d115287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115288 q = 1) (hb : d150327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115288, d150327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115289 q = 1) (hb : d150328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115289, d150328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115293 q = 1) (hb : d150330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115293, d150330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52915 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115294 q = 1) (hb : d150331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115294, d150331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115295 q = 1) (hb : d150332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115295, d150332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115296 q = 1) (hb : d150333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115296, d150333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115297 q = 1) (hb : d150334 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115297, d150334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115303 q = 1) (hb : d150340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115303, d150340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52916 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115304 q = 1) (hb : d150341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115304, d150341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115305 q = 1) (hb : d150342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115305, d150342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115306 q = 1) (hb : d150343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115306, d150343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115307 q = 1) (hb : d150344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115307, d150344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115308 q = 1) (hb : d150345 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115308, d150345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52918 (p : Pattern) (ha : d115314 p = 1) (hb : d150351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d115271 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18874 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d115272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d115273 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d115274 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d115275 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d150346 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d150346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52917 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d150347 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d150347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d150348 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d150348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d150349 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d150349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d150350 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d150350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d150351 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d115314, d150351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro52919 (p : Pattern) (ha : d115319 p = 1) (hb : d162176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115315 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115315, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115316 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115316, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115317 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115317, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115318 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115318, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115319 q = 1) (hb : d162176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d162176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52920 (p : Pattern) (ha : d115324 p = 1) (hb : d162185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115315 q = 1) (hb : d162172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115315, d162172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115316 q = 1) (hb : d162173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115316, d162173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115317 q = 1) (hb : d162174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115317, d162174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115318 q = 1) (hb : d162175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115318, d162175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12549 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12554 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115320 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115320, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115321 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115321, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115322 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115322, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115323 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115323, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115324 q = 1) (hb : d162185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115324, d162185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52921 (p : Pattern) (ha : d115331 p = 1) (hb : d163246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162180 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115320 q = 1) (hb : d162181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115320, d162181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d162182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115321, d162182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d162183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d162183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d162184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d162184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d163246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d163246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52922 (p : Pattern) (ha : d115341 p = 1) (hb : d163257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163252 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115337 q = 1) (hb : d163253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115337, d163253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12659 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d163254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115338, d163254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d163255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d163255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d163256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d163256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d163257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d163257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52923 (p : Pattern) (ha : d115347 p = 1) (hb : d163263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115325 q = 1) (hb : d162186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52919 q ha hb
    | true =>
      simp only [d115325, d162186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52920 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115326 q = 1) (hb : d162187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115326, d162187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115327 q = 1) (hb : d163244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115327, d163244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115328 q = 1) (hb : d163245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115328, d163245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115332 q = 1) (hb : d163247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115332, d163247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52921 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12590 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115333 q = 1) (hb : d163248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115333, d163248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115334 q = 1) (hb : d163249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115334, d163249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115335 q = 1) (hb : d163250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115335, d163250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115336 q = 1) (hb : d163251 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115336, d163251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115342 q = 1) (hb : d163258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115342, d163258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52922 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115343 q = 1) (hb : d163259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115343, d163259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115344 q = 1) (hb : d163260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115344, d163260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115345 q = 1) (hb : d163261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115345, d163261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115346 q = 1) (hb : d163262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115346, d163262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115347 q = 1) (hb : d163263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115347, d163263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52924 (p : Pattern) (ha : d115353 p = 1) (hb : d163269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d163264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d163264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52923 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d163265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d163265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d163266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d163266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d163267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d163267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d163268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d163268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d163269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d163269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52925 (p : Pattern) (ha : d115359 p = 1) (hb : d162327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115355 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115355, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115356 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115356, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115357 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115357, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115358 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115358, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115359 q = 1) (hb : d162327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d162327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52926 (p : Pattern) (ha : d115364 p = 1) (hb : d162336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162322 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115355 q = 1) (hb : d162323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115355, d162323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115356 q = 1) (hb : d162324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115356, d162324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115357 q = 1) (hb : d162325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115357, d162325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115358 q = 1) (hb : d162326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115358, d162326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115360 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115360, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115361 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115361, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115362 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115362, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115363 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115363, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115364 q = 1) (hb : d162336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115364, d162336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52927 (p : Pattern) (ha : d115371 p = 1) (hb : d163273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115360 q = 1) (hb : d162332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115360, d162332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d162333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115361, d162333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d162334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d162334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d162335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d162335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d163273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d163273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52928 (p : Pattern) (ha : d115381 p = 1) (hb : d163284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163279 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115377 q = 1) (hb : d163280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115377, d163280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d163281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115378, d163281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d163282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d163282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d163283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d163283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d163284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d163284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52929 (p : Pattern) (ha : d115387 p = 1) (hb : d163290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115365 q = 1) (hb : d162337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52925 q ha hb
    | true =>
      simp only [d115365, d162337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52926 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115366 q = 1) (hb : d162338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115366, d162338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115367 q = 1) (hb : d163271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115367, d163271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115368 q = 1) (hb : d163272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115368, d163272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115372 q = 1) (hb : d163274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115372, d163274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52927 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115373 q = 1) (hb : d163275 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115373, d163275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115374 q = 1) (hb : d163276 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115374, d163276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115375 q = 1) (hb : d163277 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115375, d163277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115376 q = 1) (hb : d163278 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115376, d163278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115382 q = 1) (hb : d163285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115382, d163285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52928 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12942 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115383 q = 1) (hb : d163286 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115383, d163286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115384 q = 1) (hb : d163287 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115384, d163287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115385 q = 1) (hb : d163288 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115385, d163288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115386 q = 1) (hb : d163289 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115386, d163289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115387 q = 1) (hb : d163290 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115387, d163290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52930 (p : Pattern) (ha : d115393 p = 1) (hb : d163296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d163291 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d163291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52929 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d163292 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d163292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d163293 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d163293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d163294 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d163294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d163295 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d163295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d163296 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d163296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52931 (p : Pattern) (ha : d115400 p = 1) (hb : d162502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115396 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115396, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115397 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115397, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115398 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115398, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115399 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115399, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115400 q = 1) (hb : d162502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d162502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52932 (p : Pattern) (ha : d115405 p = 1) (hb : d162512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115396 q = 1) (hb : d162498 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115396, d162498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115397 q = 1) (hb : d162499 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115397, d162499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115398 q = 1) (hb : d162500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115398, d162500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115399 q = 1) (hb : d162501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115399, d162501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13103 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13108 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115401 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115401, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115402 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115402, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115403 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115403, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115404 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115404, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115405 q = 1) (hb : d162512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115405, d162512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52933 (p : Pattern) (ha : d115412 p = 1) (hb : d163301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162507 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115401 q = 1) (hb : d162508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115401, d162508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d162509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115402, d162509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d162510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d162510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d162511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d162511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d163301 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d163301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52934 (p : Pattern) (ha : d115422 p = 1) (hb : d163316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115418 q = 1) (hb : d163312 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115418, d163312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d163313 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115419, d163313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d163314 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d163314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d163315 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d163315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d163316 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d163316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52935 (p : Pattern) (ha : d115428 p = 1) (hb : d163322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115406 q = 1) (hb : d162513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52931 q ha hb
    | true =>
      simp only [d115406, d162513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52932 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115407 q = 1) (hb : d162514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115407, d162514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115408 q = 1) (hb : d163299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115408, d163299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115409 q = 1) (hb : d163300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115409, d163300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115413 q = 1) (hb : d163302 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115413, d163302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52933 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13150 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115414 q = 1) (hb : d163303 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115414, d163303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115415 q = 1) (hb : d163304 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115415, d163304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115416 q = 1) (hb : d163305 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115416, d163305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115417 q = 1) (hb : d163306 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115417, d163306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115423 q = 1) (hb : d163317 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115423, d163317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52934 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115424 q = 1) (hb : d163318 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115424, d163318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115425 q = 1) (hb : d163319 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115425, d163319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115426 q = 1) (hb : d163320 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115426, d163320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115427 q = 1) (hb : d163321 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115427, d163321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115428 q = 1) (hb : d163322 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115428, d163322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52936 (p : Pattern) (ha : d115434 p = 1) (hb : d163328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d163323 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d163323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52935 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d163324 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d163324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d163325 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d163325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d163326 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d163326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d163327 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d163327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d163328 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d163328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52937 (p : Pattern) (ha : d115442 p = 1) (hb : d162748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115438 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115438, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115439 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115439, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115440 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115440, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115441 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115441, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115442 q = 1) (hb : d162748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d162748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52938 (p : Pattern) (ha : d115447 p = 1) (hb : d162758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115438 q = 1) (hb : d162744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115438, d162744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115439 q = 1) (hb : d162745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115439, d162745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115440 q = 1) (hb : d162746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115440, d162746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115441 q = 1) (hb : d162747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115441, d162747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115443 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115443, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115444 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115444, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115445 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115445, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115446 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115446, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115447 q = 1) (hb : d162758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115447, d162758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52939 (p : Pattern) (ha : d115454 p = 1) (hb : d163334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115443 q = 1) (hb : d162754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115443, d162754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d162755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115444, d162755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d162756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d162756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d162757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d162757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d163334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d163334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52940 (p : Pattern) (ha : d115464 p = 1) (hb : d163349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115460 q = 1) (hb : d163345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115460, d163345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13577 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d163346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115461, d163346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d163347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d163347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d163348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d163348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d163349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d163349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52941 (p : Pattern) (ha : d115470 p = 1) (hb : d163355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115448 q = 1) (hb : d162759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52937 q ha hb
    | true =>
      simp only [d115448, d162759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52938 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115449 q = 1) (hb : d162760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115449, d162760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115450 q = 1) (hb : d163332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115450, d163332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115451 q = 1) (hb : d163333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115451, d163333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115455 q = 1) (hb : d163335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115455, d163335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52939 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115456 q = 1) (hb : d163336 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115456, d163336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115457 q = 1) (hb : d163337 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115457, d163337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115458 q = 1) (hb : d163338 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115458, d163338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115459 q = 1) (hb : d163339 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115459, d163339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115465 q = 1) (hb : d163350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115465, d163350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52940 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13593 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115466 q = 1) (hb : d163351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115466, d163351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115467 q = 1) (hb : d163352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115467, d163352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115468 q = 1) (hb : d163353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115468, d163353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115469 q = 1) (hb : d163354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115469, d163354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115470 q = 1) (hb : d163355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115470, d163355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52942 (p : Pattern) (ha : d115476 p = 1) (hb : d163361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d163356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d163356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52941 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d163357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d163357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d163358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d163358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d163359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d163359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d163360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d163360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d163361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d163361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52943 (p : Pattern) (ha : d115485 p = 1) (hb : d162992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115481 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115481, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115482 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115482, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115483 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115483, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115484 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115484, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115485 q = 1) (hb : d162992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d162992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52944 (p : Pattern) (ha : d115490 p = 1) (hb : d163002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d162987 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115481 q = 1) (hb : d162988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115481, d162988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115482 q = 1) (hb : d162989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115482, d162989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115483 q = 1) (hb : d162990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115483, d162990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115484 q = 1) (hb : d162991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115484, d162991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13756 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13761 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115486 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115486, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115487 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115487, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115488 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115488, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115489 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115489, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115490 q = 1) (hb : d163002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115490, d163002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52945 (p : Pattern) (ha : d115497 p = 1) (hb : d163368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d162997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115486 q = 1) (hb : d162998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115486, d162998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d162999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115487, d162999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d163000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d163000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d163001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d163001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d163368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d163368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52946 (p : Pattern) (ha : d115507 p = 1) (hb : d163383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163378 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115503 q = 1) (hb : d163379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d163379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d163380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115504, d163380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d163381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d163381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d163382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d163382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d163383 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d163383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52947 (p : Pattern) (ha : d115513 p = 1) (hb : d163389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13653 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115491 q = 1) (hb : d163003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52943 q ha hb
    | true =>
      simp only [d115491, d163003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52944 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115492 q = 1) (hb : d163004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115492, d163004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115493 q = 1) (hb : d163366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115493, d163366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115494 q = 1) (hb : d163367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115494, d163367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115498 q = 1) (hb : d163369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115498, d163369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52945 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13803 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115499 q = 1) (hb : d163370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115499, d163370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115500 q = 1) (hb : d163371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115500, d163371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115501 q = 1) (hb : d163372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115501, d163372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115502 q = 1) (hb : d163373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115502, d163373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115508 q = 1) (hb : d163384 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115508, d163384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52946 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13920 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115509 q = 1) (hb : d163385 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115509, d163385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115510 q = 1) (hb : d163386 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115510, d163386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115511 q = 1) (hb : d163387 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115511, d163387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115512 q = 1) (hb : d163388 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115512, d163388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115513 q = 1) (hb : d163389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115513, d163389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52948 (p : Pattern) (ha : d115519 p = 1) (hb : d163395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d163390 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d163390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52947 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d163391 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d163391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d163392 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d163392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d163393 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d163393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d163394 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d163394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d163395 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d163395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52949 (p : Pattern) (ha : d115525 p = 1) (hb : d163401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d163270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52918 q ha hb
    | true =>
      simp only [d115354, d163270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52924 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d163297 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d163297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52930 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d163298 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d163298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d163329 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d163329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52936 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d163330 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d163330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d163331 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d163331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d163362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d163362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52942 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d163363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d163363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d163364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d163364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d163365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d163365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d163396 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d163396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52948 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d163397 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d163397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d163398 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d163398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d163399 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d163399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d163400 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d163400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d163401 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d163401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro52950 (p : Pattern) (ha : d115531 p = 1) (hb : d163407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d163402 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52949 q ha hb
    | true =>
      simp only [d115526, d163402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d163403 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d163403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d163404 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d163404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d163405 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d163405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d163406 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d163406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d163407 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d163407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52951 (p : Pattern) (ha : d115537 p = 1) (hb : d163413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d163408 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52950 q ha hb
    | true =>
      simp only [d115532, d163408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d163409 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d163409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d163410 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d163410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d163411 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d163411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d163412 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d163412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d163413 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d163413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52952 (p : Pattern) (ha : d115543 p = 1) (hb : d163419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d163414 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52951 q ha hb
    | true =>
      simp only [d115538, d163414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d163415 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d163415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d163416 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d163416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d163417 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d163417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d163418 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d163418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d163419 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d163419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52953 (p : Pattern) (ha : d115549 p = 1) (hb : d163425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d163420 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52952 q ha hb
    | true =>
      simp only [d115544, d163420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d163421 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d163421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d163422 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d163422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d163423 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d163423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d163424 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d163424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d163425 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d163425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52954 (p : Pattern) (ha : d115555 p = 1) (hb : d163431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d163426 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52953 q ha hb
    | true =>
      simp only [d115550, d163426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d163427 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d163427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d163428 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d163428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d163429 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d163429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d163430 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d163430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d163431 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d163431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52955 (p : Pattern) (ha : d115561 p = 1) (hb : d163437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d163432 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52954 q ha hb
    | true =>
      simp only [d115556, d163432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d163433 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d163433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d163434 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d163434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d163435 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d163435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d163436 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d163436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d163437 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d163437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52956 (p : Pattern) (ha : d115567 p = 1) (hb : d163443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d163438 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52955 q ha hb
    | true =>
      simp only [d115562, d163438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d163439 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d163439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d163440 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d163440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d163441 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d163441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d163442 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d163442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d163443 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d163443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52957 (p : Pattern) (ha : d5133 p = 1) (hb : d211415 p = 1) : d27541 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5124 q = 1) (hb : d171297 q = 1) : d5124 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5125 q = 1) (hb : d171297 q = 1) : d27538 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5125, d27538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5125, d27538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1566 q = 1) (hb : d171297 q = 1) : d1566 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5126 q = 1) (hb : d171297 q = 1) : d27539 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5126, d27539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5126, d27539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5127 q = 1) (hb : d211415 q = 1) : d27540 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5127, d211415, d27540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5127, d211415, d27540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5132 q = 1) (hb : d211415 q = 1) : d5132 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5133 q = 1) (hb : d211415 q = 1) : d27541 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5133, d27541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5133, d27541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52958 (p : Pattern) (ha : d10134 p = 1) (hb : d211415 p = 1) : d27553 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1575 q = 1) : d1575 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1576 q = 1) (hb : d171297 q = 1) : d27547 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d171297, d27547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1576, d171297, d27547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1593 q = 1) (hb : d171297 q = 1) : d27548 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d27548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1593, d27548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d10129 q = 1) : d10129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d19 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10130 q = 1) (hb : d171297 q = 1) : d27549 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d171297, d27549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d10130, d171297, d27549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d10131 q = 1) (hb : d171297 q = 1) : d27550 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d27550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10131, d27550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d10132 q = 1) (hb : d171297 q = 1) : d27551 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d27551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10132, d27551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10133 q = 1) (hb : d211415 q = 1) : d27552 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d211415, d27552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10133, d211415, d27552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10134 q = 1) (hb : d211415 q = 1) : d27553 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d27553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10134, d27553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro52959 (p : Pattern) (ha : d15166 p = 1) (hb : d211415 p = 1) : d27559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d211415 q = 1) : d27542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d27542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52957 q ha hb
    | true =>
      simp only [d5134, d27542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5135 q = 1) (hb : d211415 q = 1) : d27543 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d27543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5135, d27543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5136 q = 1) (hb : d211415 q = 1) : d27544 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d27544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d27544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d211415 q = 1) : d27545 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, d27545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5137, d27545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d211415 q = 1) : d27546 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d27546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d27546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d211415 q = 1) : d27554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52958 q ha hb
    | true =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d211415 q = 1) : d27555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d211415 q = 1) : d27556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d27556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d27556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d211415 q = 1) : d27557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d27557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d27557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d211415 q = 1) : d27558 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d27558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d27558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15166 q = 1) (hb : d211415 q = 1) : d27559 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d27559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15166, d27559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52960 (p : Pattern) (ha : d1581 p = 1) (hb : d211415 p = 1) : d27567 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1560 q = 1) : d1560 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1561 q = 1) (hb : d171297 q = 1) : d27518 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1562 q = 1) (hb : d171297 q = 1) : d27519 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1566 q = 1) (hb : d171297 q = 1) : d1566 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1567 q = 1) (hb : d171297 q = 1) : d27520 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1568 q = 1) (hb : d211415 q = 1) : d27521 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d1575 q = 1) : d1575 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d1576 q = 1) (hb : d171297 q = 1) : d27547 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d171297, d27547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d1576, d171297, d27547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h13 (q : Pattern) (ha : d1565 q = 1) (hb : d171297 q = 1) : d1565 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1577 q = 1) (hb : d171297 q = 1) : d27564 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d27564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1577, d27564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1578 q = 1) (hb : d171297 q = 1) : d1578 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1579 q = 1) (hb : d171297 q = 1) : d27565 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1579, d27565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1579, d27565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1580 q = 1) (hb : d211415 q = 1) : d27566 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1580, d211415, d27566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1580, d211415, d27566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h18 (q : Pattern) (ha : d1581 q = 1) (hb : d211415 q = 1) : d27567 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1581, d27567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1581, d27567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52961 (p : Pattern) (ha : d15171 p = 1) (hb : d211415 p = 1) : d27573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d211415 q = 1) : d27568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52960 q ha hb
    | true =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d211415 q = 1) : d27569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d211415 q = 1) : d27570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d27570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d27570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d211415 q = 1) : d27571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d27571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d27571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d211415 q = 1) : d27572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d27572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d27572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d211415 q = 1) : d27554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52958 q ha hb
    | true =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d211415 q = 1) : d27555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d211415 q = 1) : d27556 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d27556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d27556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d211415 q = 1) : d27557 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d27557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d27557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d211415 q = 1) : d27558 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d27558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d27558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15171 q = 1) (hb : d211415 q = 1) : d27573 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d27573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15171, d27573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52962 (p : Pattern) (ha : d1554 p = 1) (hb : d211415 p = 1) : d27489 p = 1 := by
  have h0 (q : Pattern) (ha : d1201 q = 1) (hb : d171297 q = 1) : d1201 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1530 q = 1) (hb : d171297 q = 1) : d27482 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1536 q = 1) (hb : d171297 q = 1) : d1536 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1537 q = 1) (hb : d171297 q = 1) : d27483 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1538 q = 1) (hb : d211415 q = 1) : d27484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d1546 q = 1) (hb : d171297 q = 1) : d27486 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1551 q = 1) (hb : d171297 q = 1) : d1551 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1552 q = 1) (hb : d171297 q = 1) : d27487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1553 q = 1) (hb : d211415 q = 1) : d27488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d1554 q = 1) (hb : d211415 q = 1) : d27489 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1554, d27489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1554, d27489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52963 (p : Pattern) (ha : d10062 p = 1) (hb : d211415 p = 1) : d27503 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10051 q = 1) (hb : d171297 q = 1) : d27500 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d27500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10051, d27500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10052 q = 1) (hb : d171297 q = 1) : d27501 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d27501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10052, d27501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d211415 q = 1) : d27502 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d211415, d27502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10053, d211415, d27502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10061 q = 1) (hb : d211415 q = 1) : d10061 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10062 q = 1) (hb : d211415 q = 1) : d27503 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10062, d27503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10062, d27503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro52964 (p : Pattern) (ha : d10073 p = 1) (hb : d211415 p = 1) : d27494 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1546 q = 1) (hb : d171297 q = 1) : d27486 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1551 q = 1) (hb : d171297 q = 1) : d1551 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1552 q = 1) (hb : d171297 q = 1) : d27487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1553 q = 1) (hb : d211415 q = 1) : d27488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10061 q = 1) (hb : d211415 q = 1) : d10061 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10073 q = 1) (hb : d211415 q = 1) : d27494 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10073, d27494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10073, d27494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro52965 (p : Pattern) (ha : d10084 p = 1) (hb : d211415 p = 1) : d27511 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10058 q = 1) (hb : d171297 q = 1) : d10058 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10080 q = 1) (hb : d171297 q = 1) : d27508 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, d27508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10080, d27508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10081 q = 1) (hb : d171297 q = 1) : d10081 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10082 q = 1) (hb : d171297 q = 1) : d27509 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, d27509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10082, d27509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10083 q = 1) (hb : d211415 q = 1) : d27510 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, d211415, d27510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10083, d211415, d27510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5132 q = 1) (hb : d211415 q = 1) : d5132 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10084 q = 1) (hb : d211415 q = 1) : d27511 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10084, d27511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10084, d27511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52966 (p : Pattern) (ha : d16791 p = 1) (hb : d211415 p = 1) : d27517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d211415 q = 1) : d27490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d27490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52962 q ha hb
    | true =>
      simp only [d1555, d27490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d211415 q = 1) : d27491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d27491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d27491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d211415 q = 1) : d27492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d27492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d27492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d211415 q = 1) : d27493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d27493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d27493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10074 q = 1) (hb : d211415 q = 1) : d27495 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d27495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52964 q ha hb
    | true =>
      simp only [d10074, d27495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10076 q = 1) (hb : d211415 q = 1) : d27496 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d27496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10076, d27496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16787 q = 1) (hb : d211415 q = 1) : d27497 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d27497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16787, d27497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16788 q = 1) (hb : d211415 q = 1) : d27498 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, d27498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16788, d27498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16789 q = 1) (hb : d211415 q = 1) : d27499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, d27499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16789, d27499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10063 q = 1) (hb : d211415 q = 1) : d27504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52963 q ha hb
    | true =>
      simp only [d10063, d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10065 q = 1) (hb : d211415 q = 1) : d27505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10065, d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15151 q = 1) (hb : d211415 q = 1) : d27506 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d27506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d27506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15152 q = 1) (hb : d211415 q = 1) : d27507 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d27507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15152, d27507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10085 q = 1) (hb : d211415 q = 1) : d27512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52965 q ha hb
    | true =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10087 q = 1) (hb : d211415 q = 1) : d27513 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15156 q = 1) (hb : d211415 q = 1) : d27514 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15157 q = 1) (hb : d211415 q = 1) : d27515 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16790 q = 1) (hb : d211415 q = 1) : d27516 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, d27516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16790, d27516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16791 q = 1) (hb : d211415 q = 1) : d27517 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, d27517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16791, d27517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro52967 (p : Pattern) (ha : d1569 p = 1) (hb : d211415 p = 1) : d27522 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1546 q = 1) (hb : d171297 q = 1) : d27486 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1546, d27486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1551 q = 1) (hb : d171297 q = 1) : d1551 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1552 q = 1) (hb : d171297 q = 1) : d27487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1552, d27487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1553 q = 1) (hb : d211415 q = 1) : d27488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1553, d211415, d27488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d1560 q = 1) : d1560 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1561 q = 1) (hb : d171297 q = 1) : d27518 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d1562 q = 1) (hb : d171297 q = 1) : d27519 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1566 q = 1) (hb : d171297 q = 1) : d1566 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1567 q = 1) (hb : d171297 q = 1) : d27520 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1568 q = 1) (hb : d211415 q = 1) : d27521 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h18 (q : Pattern) (ha : d1569 q = 1) (hb : d211415 q = 1) : d27522 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1569, d27522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1569, d27522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro52968 (p : Pattern) (ha : d10114 p = 1) (hb : d211415 p = 1) : d27527 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1543 q = 1) : d1543 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1545 q = 1) (hb : d171297 q = 1) : d27485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1545, d171297, d27485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1560 q = 1) : d1560 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1561 q = 1) (hb : d171297 q = 1) : d27518 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d1561, d171297, d27518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1562 q = 1) (hb : d171297 q = 1) : d27519 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1562, d27519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1566 q = 1) (hb : d171297 q = 1) : d1566 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1567 q = 1) (hb : d171297 q = 1) : d27520 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1567, d27520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1568 q = 1) (hb : d211415 q = 1) : d27521 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1568, d211415, d27521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5132 q = 1) (hb : d211415 q = 1) : d5132 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10114 q = 1) (hb : d211415 q = 1) : d27527 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10114, d27527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10114, d27527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro52969 (p : Pattern) (ha : d16795 p = 1) (hb : d211415 p = 1) : d27534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d211415 q = 1) : d27523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d27523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52967 q ha hb
    | true =>
      simp only [d1570, d27523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d211415 q = 1) : d27524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d27524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d27524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d211415 q = 1) : d27525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d27525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d27525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d211415 q = 1) : d27526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d27526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d27526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10115 q = 1) (hb : d211415 q = 1) : d27528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d27528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52968 q ha hb
    | true =>
      simp only [d10115, d27528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10117 q = 1) (hb : d211415 q = 1) : d27529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d27529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10117, d27529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16792 q = 1) (hb : d211415 q = 1) : d27530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d27530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16792, d27530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16793 q = 1) (hb : d211415 q = 1) : d27531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, d27531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16793, d27531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16794 q = 1) (hb : d211415 q = 1) : d27532 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, d27532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16794, d27532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d211415 q = 1) : d27512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52965 q ha hb
    | true =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d211415 q = 1) : d27513 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15156 q = 1) (hb : d211415 q = 1) : d27514 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15157 q = 1) (hb : d211415 q = 1) : d27515 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15158 q = 1) (hb : d211415 q = 1) : d27533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d27533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15158, d27533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16795 q = 1) (hb : d211415 q = 1) : d27534 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, d27534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16795, d27534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52970 (p : Pattern) (ha : d16808 p = 1) (hb : d211415 p = 1) : d27579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d211415 q = 1) : d27535 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52966 q ha hb
    | true =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d211415 q = 1) : d27536 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d211415 q = 1) : d27537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d211415 q = 1) : d27560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
    | true =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52959 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d211415 q = 1) : d27561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d211415 q = 1) : d27562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d211415 q = 1) : d27563 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16803 q = 1) (hb : d211415 q = 1) : d27574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d27574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
    | true =>
      simp only [d16803, d27574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52961 q ha hb
  have h9 (q : Pattern) (ha : d16804 q = 1) (hb : d211415 q = 1) : d27575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d27575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d27575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16805 q = 1) (hb : d211415 q = 1) : d27576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d27576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d27576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16806 q = 1) (hb : d211415 q = 1) : d27577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d27577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16806, d27577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16807 q = 1) (hb : d211415 q = 1) : d27578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16807, d27578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16807, d27578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16808 q = 1) (hb : d211415 q = 1) : d27579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16808, d27579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16808, d27579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro52971 (p : Pattern) (ha : d16812 p = 1) (hb : d211415 p = 1) : d27583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d211415 q = 1) : d27574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d27574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
    | true =>
      simp only [d16803, d27574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52961 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d211415 q = 1) : d27575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d27575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d27575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d211415 q = 1) : d27576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d27576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d27576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d211415 q = 1) : d27577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d27577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d27577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d211415 q = 1) : d27582 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d27582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d27582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16812 q = 1) (hb : d211415 q = 1) : d27583 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16812, d27583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16812, d27583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52972 (p : Pattern) (ha : d16818 p = 1) (hb : d211415 p = 1) : d27589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d211415 q = 1) : d27580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52970 q ha hb
    | true =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d211415 q = 1) : d27581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d211415 q = 1) : d27586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d211415 q = 1) : d27587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d211415 q = 1) : d27588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d27588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d27588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16818 q = 1) (hb : d211415 q = 1) : d27589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16818, d27589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16818, d27589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52973 (p : Pattern) (ha : d16822 p = 1) (hb : d211415 p = 1) : d27593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d211415 q = 1) : d27590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d211415 q = 1) : d27591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d211415 q = 1) : d27592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d27592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d27592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16822 q = 1) (hb : d211415 q = 1) : d27593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16822, d27593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16822, d27593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52974 (p : Pattern) (ha : d16828 p = 1) (hb : d211415 p = 1) : d27599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d211415 q = 1) : d27594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d27594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52972 q ha hb
    | true =>
      simp only [d16823, d27594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52973 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d211415 q = 1) : d27595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d27595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d27595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d211415 q = 1) : d27596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d27596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d27596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d211415 q = 1) : d27597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d27597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d27597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d211415 q = 1) : d27598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d27598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d27598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16828 q = 1) (hb : d211415 q = 1) : d27599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16828, d27599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16828, d27599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52975 (p : Pattern) (ha : d16831 p = 1) (hb : d211415 p = 1) : d27602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d211415 q = 1) : d27580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52970 q ha hb
    | true =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d211415 q = 1) : d27581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d211415 q = 1) : d27586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d211415 q = 1) : d27587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16817 q = 1) (hb : d211415 q = 1) : d27588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16817, d27588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16817, d27588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16831 q = 1) (hb : d211415 q = 1) : d27602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16831, d27602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16831, d27602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro52976 (p : Pattern) (ha : d16832 p = 1) (hb : d211415 p = 1) : d27603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d211415 q = 1) : d27590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d211415 q = 1) : d27591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16821 q = 1) (hb : d211415 q = 1) : d27592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16821, d27592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16821, d27592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16832 q = 1) (hb : d211415 q = 1) : d27603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16832, d27603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16832, d27603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52977 (p : Pattern) (ha : d16838 p = 1) (hb : d211415 p = 1) : d27609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16823 q = 1) (hb : d211415 q = 1) : d27594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16823, d27594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52972 q ha hb
    | true =>
      simp only [d16823, d27594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52973 q ha hb
  have h2 (q : Pattern) (ha : d16824 q = 1) (hb : d211415 q = 1) : d27595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16824, d27595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16824, d27595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16825 q = 1) (hb : d211415 q = 1) : d27596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16825, d27596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16825, d27596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16826 q = 1) (hb : d211415 q = 1) : d27597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16826, d27597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16826, d27597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16827 q = 1) (hb : d211415 q = 1) : d27598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16827, d27598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16827, d27598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16833 q = 1) (hb : d211415 q = 1) : d27604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d27604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52975 q ha hb
    | true =>
      simp only [d16833, d27604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52976 q ha hb
  have h7 (q : Pattern) (ha : d16834 q = 1) (hb : d211415 q = 1) : d27605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d27605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d27605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16835 q = 1) (hb : d211415 q = 1) : d27606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d27606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16835, d27606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16836 q = 1) (hb : d211415 q = 1) : d27607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d27607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d27607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16837 q = 1) (hb : d211415 q = 1) : d27608 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d27608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d27608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16838 q = 1) (hb : d211415 q = 1) : d27609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16838, d27609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16838, d27609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52978 (p : Pattern) (ha : d16879 p = 1) (hb : d211415 p = 1) : d27666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d211415 q = 1) : d27535 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52966 q ha hb
    | true =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d211415 q = 1) : d27536 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d211415 q = 1) : d27537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d211415 q = 1) : d27560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
    | true =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52959 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d211415 q = 1) : d27561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d211415 q = 1) : d27562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d211415 q = 1) : d27563 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d211415 q = 1) : d27664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d27664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d27664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d211415 q = 1) : d27665 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d27665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d27665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16879 q = 1) (hb : d211415 q = 1) : d27666 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16879, d27666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16879, d27666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro52979 (p : Pattern) (ha : d16889 p = 1) (hb : d211415 p = 1) : d27676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16880 q = 1) (hb : d211415 q = 1) : d27667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52978 q ha hb
    | true =>
      simp only [d16880, d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16881 q = 1) (hb : d211415 q = 1) : d27668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16886 q = 1) (hb : d211415 q = 1) : d27673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16886, d27673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16886, d27673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16887 q = 1) (hb : d211415 q = 1) : d27674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16887, d27674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16887, d27674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16888 q = 1) (hb : d211415 q = 1) : d27675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16888, d27675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16888, d27675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16889 q = 1) (hb : d211415 q = 1) : d27676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16889, d27676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16889, d27676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52980 (p : Pattern) (ha : d16983 p = 1) (hb : d211415 p = 1) : d27848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16973 q = 1) (hb : d211415 q = 1) : d27838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16973, d27838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52979 q ha hb
    | true =>
      simp only [d16973, d27838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52973 q ha hb
  have h2 (q : Pattern) (ha : d16974 q = 1) (hb : d211415 q = 1) : d27839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16974, d27839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16974, d27839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16975 q = 1) (hb : d211415 q = 1) : d27840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16975, d27840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16975, d27840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16976 q = 1) (hb : d211415 q = 1) : d27841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16976, d27841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16976, d27841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16977 q = 1) (hb : d211415 q = 1) : d27842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16977, d27842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16977, d27842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16978 q = 1) (hb : d211415 q = 1) : d27843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d27843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52973 q ha hb
    | true =>
      simp only [d16978, d27843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16979 q = 1) (hb : d211415 q = 1) : d27844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d27844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d27844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16980 q = 1) (hb : d211415 q = 1) : d27845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d27845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16980, d27845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16981 q = 1) (hb : d211415 q = 1) : d27846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d27846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d27846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16982 q = 1) (hb : d211415 q = 1) : d27847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d27847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d27847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16983 q = 1) (hb : d211415 q = 1) : d27848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16983, d27848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16983, d27848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52981 (p : Pattern) (ha : d16989 p = 1) (hb : d211415 p = 1) : d27854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16978 q = 1) (hb : d211415 q = 1) : d27843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16978, d27843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52973 q ha hb
    | true =>
      simp only [d16978, d27843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16979 q = 1) (hb : d211415 q = 1) : d27844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16979, d27844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16979, d27844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16980 q = 1) (hb : d211415 q = 1) : d27845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16980, d27845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16980, d27845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16981 q = 1) (hb : d211415 q = 1) : d27846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16981, d27846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16981, d27846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16982 q = 1) (hb : d211415 q = 1) : d27847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16982, d27847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16982, d27847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16984 q = 1) (hb : d211415 q = 1) : d27849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d27849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52976 q ha hb
    | true =>
      simp only [d16984, d27849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16985 q = 1) (hb : d211415 q = 1) : d27850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d27850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d27850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16986 q = 1) (hb : d211415 q = 1) : d27851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d27851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16986, d27851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16987 q = 1) (hb : d211415 q = 1) : d27852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d27852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d27852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16988 q = 1) (hb : d211415 q = 1) : d27853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d27853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d27853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16989 q = 1) (hb : d211415 q = 1) : d27854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16989, d27854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16989, d27854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52982 (p : Pattern) (ha : d16998 p = 1) (hb : d211415 p = 1) : d27863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16984 q = 1) (hb : d211415 q = 1) : d27849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16984, d27849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52976 q ha hb
    | true =>
      simp only [d16984, d27849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16985 q = 1) (hb : d211415 q = 1) : d27850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16985, d27850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16985, d27850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16986 q = 1) (hb : d211415 q = 1) : d27851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16986, d27851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16986, d27851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16987 q = 1) (hb : d211415 q = 1) : d27852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16987, d27852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16987, d27852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16988 q = 1) (hb : d211415 q = 1) : d27853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16988, d27853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16988, d27853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16998 q = 1) (hb : d211415 q = 1) : d27863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16998, d27863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16998, d27863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52983 (p : Pattern) (ha : d15435 p = 1) (hb : d211415 p = 1) : d27959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d211415 q = 1) : d27954 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d27954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d27954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52960 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d211415 q = 1) : d27568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52960 q ha hb
    | true =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d211415 q = 1) : d27955 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d27955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d27955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d211415 q = 1) : d27569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d211415 q = 1) : d27956 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d27956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d27956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d211415 q = 1) : d27957 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d27957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d27957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d211415 q = 1) : d27958 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d27958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d27958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d211415 q = 1) : d27931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d27931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d27931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52958 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d211415 q = 1) : d27554 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52958 q ha hb
    | true =>
      simp only [d10135, d27554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d211415 q = 1) : d27932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d27932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d27932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d211415 q = 1) : d27555 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d27555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d211415 q = 1) : d27933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d27933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d27933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d211415 q = 1) : d27934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d27934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d27934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d211415 q = 1) : d27935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d27935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d27935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15435 q = 1) (hb : d211415 q = 1) : d27959 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d27959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15435, d27959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro52984 (p : Pattern) (ha : d17032 p = 1) (hb : d211415 p = 1) : d27922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d211415 q = 1) : d27913 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d27913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d27913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52967 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d211415 q = 1) : d27523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d27523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52967 q ha hb
    | true =>
      simp only [d1570, d27523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d211415 q = 1) : d27914 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d27914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d27914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d211415 q = 1) : d27524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d27524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d27524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d211415 q = 1) : d27915 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d27915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d27915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d211415 q = 1) : d27916 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d27916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d27916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17027 q = 1) (hb : d211415 q = 1) : d27917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d27917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d27917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52968 q ha hb
  have h8 (q : Pattern) (ha : d10115 q = 1) (hb : d211415 q = 1) : d27528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d27528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52968 q ha hb
    | true =>
      simp only [d10115, d27528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d211415 q = 1) : d27918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d27918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17028, d27918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10117 q = 1) (hb : d211415 q = 1) : d27529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d27529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10117, d27529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17029 q = 1) (hb : d211415 q = 1) : d27919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d27919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17029, d27919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17030 q = 1) (hb : d211415 q = 1) : d27920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d27920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17030, d27920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d17031 q = 1) (hb : d211415 q = 1) : d27921 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d27921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17031, d27921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15397 q = 1) (hb : d211415 q = 1) : d27893 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d27893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52965 q ha hb
  have h15 (q : Pattern) (ha : d10085 q = 1) (hb : d211415 q = 1) : d27512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52965 q ha hb
    | true =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d15398 q = 1) (hb : d211415 q = 1) : d27894 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15398, d27894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10087 q = 1) (hb : d211415 q = 1) : d27513 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15399 q = 1) (hb : d211415 q = 1) : d27895 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15399, d27895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15400 q = 1) (hb : d211415 q = 1) : d27896 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d27896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15400, d27896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d15401 q = 1) (hb : d211415 q = 1) : d27907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d27907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15401, d27907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d17032 q = 1) (hb : d211415 q = 1) : d27922 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d27922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d17032, d27922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro52985 (p : Pattern) (ha : d17058 p = 1) (hb : d211415 p = 1) : d27965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d211415 q = 1) : d27960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d27960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52984 q ha hb
    | true =>
      simp only [d17053, d27960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52983 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d211415 q = 1) : d27961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d27961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d27961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d211415 q = 1) : d27962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d27962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d27962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d211415 q = 1) : d27963 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d27963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d27963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d211415 q = 1) : d27964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d27964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d27964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17058 q = 1) (hb : d211415 q = 1) : d27965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17058, d27965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17058, d27965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52986 (p : Pattern) (ha : d17130 p = 1) (hb : d211415 p = 1) : d28072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17059 q = 1) (hb : d211415 q = 1) : d27966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52985 q ha hb
    | true =>
      simp only [d17059, d27966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17060 q = 1) (hb : d211415 q = 1) : d27967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d27967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17127 q = 1) (hb : d211415 q = 1) : d28069 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17127, d28069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17127, d28069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17128 q = 1) (hb : d211415 q = 1) : d28070 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17128, d28070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17128, d28070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17129 q = 1) (hb : d211415 q = 1) : d28071 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17129, d28071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17129, d28071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17130 q = 1) (hb : d211415 q = 1) : d28072 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17130, d28072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17130, d28072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro52987 (p : Pattern) (ha : d17136 p = 1) (hb : d211415 p = 1) : d28078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17131 q = 1) (hb : d211415 q = 1) : d28073 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17131, d28073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52986 q ha hb
    | true =>
      simp only [d17131, d28073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17132 q = 1) (hb : d211415 q = 1) : d28074 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17132, d28074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17132, d28074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17133 q = 1) (hb : d211415 q = 1) : d28075 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17133, d28075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17133, d28075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17134 q = 1) (hb : d211415 q = 1) : d28076 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17134, d28076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17134, d28076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17135 q = 1) (hb : d211415 q = 1) : d28077 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17135, d28077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17135, d28077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17136 q = 1) (hb : d211415 q = 1) : d28078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17136, d28078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17136, d28078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52988 (p : Pattern) (ha : d16843 p = 1) (hb : d211415 p = 1) : d27614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d211415 q = 1) : d27580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52970 q ha hb
    | true =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d211415 q = 1) : d27581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d211415 q = 1) : d27586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16816 q = 1) (hb : d211415 q = 1) : d27587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16816, d27587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16842 q = 1) (hb : d211415 q = 1) : d27613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16842, d27613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16842, d27613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16843 q = 1) (hb : d211415 q = 1) : d27614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16843, d27614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16843, d27614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52989 (p : Pattern) (ha : d16845 p = 1) (hb : d211415 p = 1) : d27616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d211415 q = 1) : d27590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16820 q = 1) (hb : d211415 q = 1) : d27591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16820, d27591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16844 q = 1) (hb : d211415 q = 1) : d27615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16844, d27615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16844, d27615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16845 q = 1) (hb : d211415 q = 1) : d27616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16845, d27616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16845, d27616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52990 (p : Pattern) (ha : d16852 p = 1) (hb : d211415 p = 1) : d27623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16809 q = 1) (hb : d211415 q = 1) : d27580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52970 q ha hb
    | true =>
      simp only [d16809, d27580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16810 q = 1) (hb : d211415 q = 1) : d27581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16810, d27581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16815 q = 1) (hb : d211415 q = 1) : d27586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16815, d27586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16850 q = 1) (hb : d211415 q = 1) : d27621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16850, d27621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16850, d27621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16851 q = 1) (hb : d211415 q = 1) : d27622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16851, d27622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16851, d27622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16852 q = 1) (hb : d211415 q = 1) : d27623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16852, d27623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16852, d27623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52991 (p : Pattern) (ha : d16855 p = 1) (hb : d211415 p = 1) : d27626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16813 q = 1) (hb : d211415 q = 1) : d27584 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52971 q ha hb
    | true =>
      simp only [d16813, d27584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16814 q = 1) (hb : d211415 q = 1) : d27585 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16814, d27585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16819 q = 1) (hb : d211415 q = 1) : d27590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16819, d27590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16853 q = 1) (hb : d211415 q = 1) : d27624 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16853, d27624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16853, d27624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16854 q = 1) (hb : d211415 q = 1) : d27625 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16854, d27625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16854, d27625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16855 q = 1) (hb : d211415 q = 1) : d27626 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16855, d27626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16855, d27626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro52992 (p : Pattern) (ha : d1664 p = 1) (hb : d211415 p = 1) : d27630 p = 1 := by
  have h0 (q : Pattern) (ha : d1663 q = 1) (hb : d211415 q = 1) : d1663 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1201 q = 1) (hb : d171297 q = 1) : d1201 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1530 q = 1) (hb : d171297 q = 1) : d27482 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1536 q = 1) (hb : d171297 q = 1) : d1536 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1537 q = 1) (hb : d171297 q = 1) : d27483 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1538 q = 1) (hb : d211415 q = 1) : d27484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1664 q = 1) (hb : d211415 q = 1) : d27630 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1664, d27630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1664, d27630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52993 (p : Pattern) (ha : d10035 p = 1) (hb : d211415 p = 1) : d27635 p = 1 := by
  have h0 (q : Pattern) (ha : d1201 q = 1) (hb : d171297 q = 1) : d1201 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1530 q = 1) (hb : d171297 q = 1) : d27482 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1530, d27482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1536 q = 1) (hb : d171297 q = 1) : d1536 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1537 q = 1) (hb : d171297 q = 1) : d27483 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1537, d27483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1538 q = 1) (hb : d211415 q = 1) : d27484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1538, d211415, d27484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10035 q = 1) (hb : d211415 q = 1) : d27635 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10035, d27635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10035, d27635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52994 (p : Pattern) (ha : d16863 p = 1) (hb : d211415 p = 1) : d27642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d211415 q = 1) : d27631 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d27631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52992 q ha hb
    | true =>
      simp only [d1665, d27631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d211415 q = 1) : d27632 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d27632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d27632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d211415 q = 1) : d27633 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d27633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d27633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d211415 q = 1) : d27634 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d27634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d27634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10036 q = 1) (hb : d211415 q = 1) : d27636 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d27636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52993 q ha hb
    | true =>
      simp only [d10036, d27636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10038 q = 1) (hb : d211415 q = 1) : d27637 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d27637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10038, d27637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16859 q = 1) (hb : d211415 q = 1) : d27638 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d27638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d27638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16860 q = 1) (hb : d211415 q = 1) : d27639 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d27639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16860, d27639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16861 q = 1) (hb : d211415 q = 1) : d27640 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, d27640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16861, d27640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15230 q = 1) (hb : d211415 q = 1) : d15230 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10063 q = 1) (hb : d211415 q = 1) : d27504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52963 q ha hb
    | true =>
      simp only [d10063, d27504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10065 q = 1) (hb : d211415 q = 1) : d27505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10065, d27505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15151 q = 1) (hb : d211415 q = 1) : d27506 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d27506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d27506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15152 q = 1) (hb : d211415 q = 1) : d27507 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, d27507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15152, d27507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16862 q = 1) (hb : d211415 q = 1) : d27641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, d27641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16862, d27641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16863 q = 1) (hb : d211415 q = 1) : d27642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, d27642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16863, d27642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro52995 (p : Pattern) (ha : d10098 p = 1) (hb : d211415 p = 1) : d27649 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1527 q = 1) : d1527 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1529 q = 1) (hb : d171297 q = 1) : d27481 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1529, d171297, d27481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10056 q = 1) (hb : d171297 q = 1) : d10056 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10095 q = 1) (hb : d171297 q = 1) : d27646 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10095, d27646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10095, d27646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d171297 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10096 q = 1) (hb : d171297 q = 1) : d27647 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10096, d27647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10096, d27647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10097 q = 1) (hb : d211415 q = 1) : d27648 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10097, d211415, d27648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10097, d211415, d27648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10061 q = 1) (hb : d211415 q = 1) : d10061 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10098 q = 1) (hb : d211415 q = 1) : d27649 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10098, d27649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10098, d27649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro52996 (p : Pattern) (ha : d16868 p = 1) (hb : d211415 p = 1) : d27655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d211415 q = 1) : d27650 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d27650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52995 q ha hb
    | true =>
      simp only [d10099, d27650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10101 q = 1) (hb : d211415 q = 1) : d27651 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d27651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10101, d27651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13348 q = 1) (hb : d211415 q = 1) : d27652 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d27652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d27652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d211415 q = 1) : d27653 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, d27653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13349, d27653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10085 q = 1) (hb : d211415 q = 1) : d27512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52965 q ha hb
    | true =>
      simp only [d10085, d27512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10087 q = 1) (hb : d211415 q = 1) : d27513 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10087, d27513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15156 q = 1) (hb : d211415 q = 1) : d27514 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d27514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15157 q = 1) (hb : d211415 q = 1) : d27515 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15157, d27515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16867 q = 1) (hb : d211415 q = 1) : d27654 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, d27654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16867, d27654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15158 q = 1) (hb : d211415 q = 1) : d27533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d27533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15158, d27533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16868 q = 1) (hb : d211415 q = 1) : d27655 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, d27655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16868, d27655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro52997 (p : Pattern) (ha : d16874 p = 1) (hb : d211415 p = 1) : d27661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d211415 q = 1) : d27643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d27643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52994 q ha hb
    | true =>
      simp only [d16864, d27643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52966 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d211415 q = 1) : d27644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d27644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d27644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d211415 q = 1) : d27645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d27645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d27645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d211415 q = 1) : d27656 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d27656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52966 q ha hb
    | true =>
      simp only [d16869, d27656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52996 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d211415 q = 1) : d27657 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d27657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d27657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d211415 q = 1) : d27658 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d27658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d27658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d211415 q = 1) : d27659 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d27659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d27659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d211415 q = 1) : d27535 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52966 q ha hb
    | true =>
      simp only [d16796, d27535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d211415 q = 1) : d27536 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d27536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d211415 q = 1) : d27537 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d27537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d211415 q = 1) : d27560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52969 q ha hb
    | true =>
      simp only [d16799, d27560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52959 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d211415 q = 1) : d27561 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d27561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d211415 q = 1) : d27562 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d27562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d211415 q = 1) : d27563 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d27563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d211415 q = 1) : d27660 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d27660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d27660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16874 q = 1) (hb : d211415 q = 1) : d27661 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16874, d27661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16874, d27661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro52998 (p : Pattern) (ha : d16885 p = 1) (hb : d211415 p = 1) : d27672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16875 q = 1) (hb : d211415 q = 1) : d27662 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16875, d27662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52997 q ha hb
    | true =>
      simp only [d16875, d27662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16876 q = 1) (hb : d211415 q = 1) : d27663 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16876, d27663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16876, d27663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16880 q = 1) (hb : d211415 q = 1) : d27667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16880, d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52978 q ha hb
    | true =>
      simp only [d16880, d27667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16881 q = 1) (hb : d211415 q = 1) : d27668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16881, d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16881, d27668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16882 q = 1) (hb : d211415 q = 1) : d27669 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16882, d27669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16882, d27669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16883 q = 1) (hb : d211415 q = 1) : d27670 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16883, d27670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16883, d27670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16884 q = 1) (hb : d211415 q = 1) : d27671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16884, d27671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16884, d27671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16885 q = 1) (hb : d211415 q = 1) : d27672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16885, d27672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16885, d27672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro52999 (p : Pattern) (ha : d13287 p = 1) (hb : d211415 p = 1) : d27793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d211415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d211415 q = 1) : d27568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52960 q ha hb
    | true =>
      simp only [d1582, d27568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d211415 q = 1) : d27569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d27569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d211415 q = 1) : d27570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d27570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d27570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d211415 q = 1) : d27571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d27571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d27571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d211415 q = 1) : d27572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d27572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d27572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d211415 q = 1) : d27793 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d27793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, d27793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
